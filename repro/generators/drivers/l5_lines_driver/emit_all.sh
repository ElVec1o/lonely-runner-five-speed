#!/bin/bash
# emit_all.sh [FIRST_BATCH [LAST_BATCH]] : RESUMABLE emission of the all-tree lines certificate (81,436 classes, 1,063 chunk modules LinRQ<node>C<j>).
#   plan.tsv (deterministic: nodes by ascending points, node 5 last, chunks <= 15,000 visited points; made by `l5qemit plan`) is cut into batches of
#   BATCH (50) plan lines; batch b -> $SRCC/batch_NNNN/*.lean + MANIFEST.sha256 + .done.  A batch with .done is skipped; one generator process,
#   ceiling 790 MB (peak about 400 MB, independent of the batch index: every chunk module is a separate file and every class is generated from scratch),
#   disk gate (free >= 5 GB) and a source budget (sum of src_chunks + src_asm <= 1 GB), no Lean, no Python.
#   Every class is also run through the independent interpreter of the Lean text (decoded from the emitted hex); exit 7 if any is rejected.
#   The driver calls this lazily: `emit_all.sh B B` just before the first chunk of batch B is built.
. /DEV_TREE/work/l5_lines_driver/common.sh
NPLAN=$(wc -l < $PLAN); NB=$(( (NPLAN + BATCH - 1) / BATCH ))
FIRST=${1:-0}; LAST=${2:-$((NB - 1))}
mkdir -p $SRCC $RO/logs/emit
for b in $(seq $FIRST $LAST); do
  D=$SRCC/batch_$(printf %04d $b)
  [ -f $D/.done ] && continue
  FREE=$(free_gb); [ "$FREE" -lt $DISK_FLOOR_GB ] && { echo "batch $b: STOP, free disk ${FREE} GB below floor ${DISK_FLOOR_GB} GB"; exit 3; }
  USED=$(du -sm $SRCC $RO/src_asm 2>/dev/null | awk '{s+=$1} END{print s+0}')
  [ "$USED" -gt $SRC_BUDGET_MB ] && { echo "batch $b: STOP, source budget ${USED} MB > ${SRC_BUDGET_MB} MB"; exit 6; }
  lo=$((b * BATCH)); hi=$((lo + BATCH)); [ $hi -gt $NPLAN ] && hi=$NPLAN
  rm -rf $D; mkdir -p $D
  bash $LAUNCH_SMALL 790 $RO/logs/emit emit_b$b $EMIT emitc $TDIR $TSV $LINTL all $PLAN $D $lo $hi
  grep -q '^exit=0' $RO/logs/emit/emit_b$b.watch && ! grep -q WATCHDOG $RO/logs/emit/emit_b$b.watch || { echo "batch $b FAILED (logs/emit/emit_b$b.*)"; exit 4; }
  grep -q 'interpreter rejected 0' $RO/logs/emit/emit_b$b.err || { echo "batch $b: interpreter rejected a class"; exit 7; }
  N=$(ls $D | grep -c '\.lean$'); [ "$N" -eq $((hi - lo)) ] || { echo "batch $b: expected $((hi - lo)) files, found $N"; exit 5; }
  (cd $D && shasum -a 256 *.lean > MANIFEST.sha256)
  touch $D/.done
  echo "batch $b: $((hi - lo)) chunks emitted ($(du -sm $D | cut -f1) MB)"
done
# global manifest (all finished batches, sorted by file name)
cat $SRCC/batch_*/MANIFEST.sha256 2>/dev/null | sort -k2 > $RO/MANIFEST.sha256
