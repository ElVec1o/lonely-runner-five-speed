#!/bin/bash
# emit_all.sh: regenerate the five-speed Lean data sources in batches.  Resumable (a batch directory with a .done marker is skipped),
# one generator process, ceiling 790 MB (measured peak 120-300 MB), no Lean, no Python, disk gate (free GB on the data volume).
# Usage:  emit_all.sh [FIRST_BATCH [LAST_BATCH]]        batch b = representatives 50 b .. 50 b + 49  (1,965 reps = 40 batches, 0..39)
# Env:    BATCH (50)  DISK_FLOOR_GB (5)  ROOT (this directory)
#   V3=0 (default): the old v1 generator l5d, modes emit+leaves (per-node-chunk leaf modules), CHUNK default 1300, output src/.
#   V3=1          : the v3 generator l5v3 (gen3/), modes emit+v3 (flat layout: GD3N* node modules, GD3F2N<rep> node accessor,
#                   GD3F2L<rep>R<j> per-record chunk modules, GD3F2L<rep> assembly); CHUNK default 1700 (the node-module size of the
#                   validated block-11 modules, so nmods agrees with the lean tree); output src_v3<TAG>/ ; manifest MANIFEST_v3<TAG>.sha256
#   V3 options: PR (64 records per chunk module), LAYOUT=A (conv.rs-compatible text, all 32-bit digits, default) or U (uniform per-chunk
#               interface recsU_cj / recsU_ok_cj, needed for 16-bit chunks and critical chunks), W16=1 (U only: a chunk whose digits all
#               satisfy |x| <= 32767 is written with 16-bit digits and the accessor dg16 of proposed/GD3F4.lean), TAG (suffix of the output dir).
# Reps with critical leaves (only #304) get node modules and a sidecar line in logs/v3<TAG>/v3_crit_v3.tsv but NO flat leaf modules.
set -u
ROOT=${ROOT:-/DEV_TREE/work/lean5_data}
LAUNCH=/DEV_TREE/work/l5probe4/launch_nogate.sh
V3=${V3:-0}; TAG=${TAG:-}
BATCH=${BATCH:-50}; FLOOR=${DISK_FLOOR_GB:-5}
NREP=1965
FIRST=${1:-0}; LAST=${2:-$(( (NREP + BATCH - 1) / BATCH - 1 ))}
if [ "$V3" = 1 ]; then
  G=$ROOT/gen3/target/release/l5v3; GDIR=$ROOT/gen3; CHUNK=${CHUNK:-1700}; SRC=$ROOT/src_v3$TAG; MODES="emit v3"; MAN=$ROOT/MANIFEST_v3$TAG.sha256; LOGR=$ROOT/logs/v3$TAG
  export L5V3_PR=${PR:-64} L5V3_LAYOUT=${LAYOUT:-A} L5V3_W16=${W16:-0}
else
  G=$ROOT/gen/target/release/l5d; GDIR=$ROOT/gen; CHUNK=${CHUNK:-1300}; SRC=$ROOT/src; MODES="emit leaves"; MAN=$ROOT/MANIFEST.sha256; LOGR=$ROOT/logs
fi
[ -x "$G" ] || { (cd "$GDIR" && PATH=$PATH:$HOME/.cargo/bin cargo build --release) || exit 2; }
mkdir -p "$SRC" "$ROOT/logs/runs" "$LOGR"
for b in $(seq $FIRST $LAST); do
  D=$SRC/batch_$(printf %04d $b)
  [ -f "$D/.done" ] && { echo "batch $b: done, skipped"; continue; }
  FREE=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  [ "$FREE" -lt "$FLOOR" ] && { echo "batch $b: STOP, free disk ${FREE} GB below floor ${FLOOR} GB"; exit 3; }
  lo=$((b * BATCH)); hi=$((lo + BATCH - 1)); [ $hi -ge $NREP ] && hi=$((NREP - 1))
  IDS=$(seq -s, $lo $hi | sed 's/,$//')
  rm -rf "$D"; mkdir -p "$D"
  for MODE in $MODES; do
    L5D_SRC=$D L5D_LOG=$LOGR/emit_b$b bash "$LAUNCH" 790 "$ROOT/logs/runs" "emit${TAG}_V${V3}_b${b}_$MODE" "$G" $MODE "$IDS" $CHUNK >/dev/null 2>&1
    grep -q '^exit=0' "$ROOT/logs/runs/emit${TAG}_V${V3}_b${b}_$MODE.watch" || { echo "batch $b mode $MODE FAILED (see logs/runs/emit${TAG}_V${V3}_b${b}_$MODE.*)"; exit 4; }
    grep -q WATCHDOG "$ROOT/logs/runs/emit${TAG}_V${V3}_b${b}_$MODE.watch" && { echo "batch $b: watchdog fired"; exit 5; }
  done
  (cd "$D" && ls *.lean >/dev/null 2>&1 && shasum -a 256 *.lean > MANIFEST.sha256 || : > MANIFEST.sha256)
  touch "$D/.done"; echo "batch $b: reps $lo..$hi, $(ls $D | grep -c '\.lean$') files, $(du -sk $D | cut -f1) KB"
done
# global manifest (sha256 of every generated file, relative to the source root)
(cd "$SRC" && for d in batch_*; do [ -f $d/.done ] && sed "s|  |  $d/|" $d/MANIFEST.sha256; done > "$MAN")
echo "manifest: $(wc -l < $MAN) files -> $MAN"
