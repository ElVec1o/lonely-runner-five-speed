#!/bin/bash
# regen_data.sh : regenerate the Rust-generated Lean sources of the five-speed proof and compare them BYTE FOR BYTE with the manifest (sha256).
#
# The generated modules are an UNTRUSTED ORACLE: the Lean kernel re-checks every generated blob against definitions whose soundness is
# proved in Lean, so a wrong generator can only make the build fail, never prove something false.  This script is for reproducibility.
#
# USAGE   bash regen_data.sh [--sample | --full] [--steps build,v3,s4o,lines,reg,agg,hl] [--keep] [--install]
#   --sample (default)  bounded sample, minutes: reps SAMPLE_REPS through v3 + s4o, three slices of the lines plan, Reg for REG_REPS,
#                       and the COMPLETE regeneration of the aggregation (AggFive, 396 files + L5S5/FiveSpeedFinal) and of the mirror (AggFive/Hl, 314)
#   --full              v3 + s4o for ALL reps (the eight DONE_PRIOR reps excluded, see below), lines for ALL 1,053 plan chunks, in batches
#                       of 50 reps / 50 plan lines (temporary files removed after each batch).  Writes about 0.8 GB at a time at most.
#   --install           (with --full) copy every regenerated file whose sha256 equals the manifest into LEAN_DIR, ONLY where no file exists yet
#                       (this is how the omitted families l5s4o `GD3O*` and l5qemit `LinRQSC*` are restored on a machine that has only the bundle)
# WHAT IT COMPARES   Every produced file is compared with the sha256 in MANIFEST.tsv (path relative to the lean/ directory) or, for the intermediate
#   blobs `GD3F2L<rep>R<j>` that are deleted from the Lean tree after use, with inputs/MANIFEST_v3r.sha256.  The summary prints identical /
#   different / not-in-reference counts per step; exit 0 only if no file differs and at least one was compared.
# NOT COVERED (stated plainly)   eight reps of the l5s4o family: 265 and 304 (big-rep / critical-leaf chains, lean5_crit; our run of l5s4o on rep 265 gives
#   different files) and 927, 1075, 1336, 1343, 1524, 1763 (built by the earlier S4O stage with 64-record chunks: `GD3O<rep>Rall`, different chunking); their
#   `GD3O<rep>*` modules are listed in the manifest as generator l5s4o? but are NOT reproduced here (OBSERVED: running l5s4o on the six gives different files); the T2 families (l5s4r_gen, l5s4s_gen), l5s4k_gen headers (GD3N*, reproduced here by the v3 emitter l5v3), l5s4e/f_gen, L5WP1 box
#   data, LinRQSG/LinRAll assembly modules, RegP*/RegFin* (only `Reg<rep>` and `Mem` are sampled); sources of those generators are in generators/
#   but this script does not run them (their sources are shipped inside the bundle's lean/ tree with manifest hashes).
# INPUTS (copied into inputs/, see inputs/INPUTS.sha256): plan.tsv, t4_classes.tsv, src_t4_all/ (T4 class tables written by an earlier stage of l5v3),
#   modname.tsv, rollout_results.tsv, T2RL_STATUS.tsv, extra_built.txt, MANIFEST_v3r.sha256.  Steps reg, agg, hl additionally READ a lean tree
#   (LEAN_DIR: L5S4 sources, and the .lake build for the "which reps are built" decision); they write only under work/.
# SAFETY: the generator copies are PATCHED with sed (the placeholder path prefix /DEV_TREE of the shipped sources -> work/ and inputs/) so that nothing is written into
#   LEAN_DIR or into any state directory; the sources in generators/ stay unchanged.
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
LAUNCH=${LAUNCH:-}   # optional launcher: script called as LAUNCH CEILING_MB LOGDIR NAME cmd...
SMALL_CEILING_MB=${SMALL_CEILING_MB:-790}
GEN=$HERE/generators; IN=$HERE/inputs; WORK=${WORK:-$HERE/work}; L=$HERE/logs/regen
MODE=sample; STEPS=build,v3,s4o,lines,reg,agg,hl; KEEP=0; INSTALL=0
SAMPLE_REPS=${SAMPLE_REPS:-"0 1 2 3 4 5 8 11 100 101 262 264 272 286"}
REG_REPS=${REG_REPS:-"5 11 100 272 286"}
LINES_SLICES=${LINES_SLICES:-"0:3 500:503 1050:1053"}
NREP=1965; PLANN=$(wc -l < "$IN/plan.tsv" | tr -d ' ')
# reps NOT produced by this chain: the rollout marks them DONE_PRIOR (265 and 304: big-rep and critical-leaf chains; 927, 1075, 1336, 1343, 1524, 1763:
# built by the earlier S4O stage with 64-record chunk modules `GD3O<rep>Rall` etc.): skipped, listed in the summary
SKIP_REPS=" $(awk -F'\t' '$2=="DONE_PRIOR"{printf "%s ", $1}' "$IN/rollout_results.tsv") "
while [ $# -gt 0 ]; do case "$1" in
  --sample) MODE=sample ;; --full) MODE=full ;; --steps) STEPS=$2; shift ;; --keep) KEEP=1 ;; --install) INSTALL=1 ;;
  -h|--help) sed -n '2,32p' "$0"; exit 0 ;; *) echo "unknown option $1" >&2; exit 2 ;; esac; shift; done
mkdir -p "$WORK" "$L"
step() { case ",$STEPS," in *",$1,"*) return 0 ;; *) return 1 ;; esac; }
NSAME=0; NDIFF=0; NNOREF=0
export CARGO_TARGET_DIR=$WORK/target
BIN=$WORK/target/release

small() { # NAME cmd... : run one small job under the programme's launch_job.sh when present; return the job's exit code
  local name=$1; shift
  rm -f "${L:?}/${name:?}.out" "${L:?}/${name:?}.err" "${L:?}/${name:?}.watch"
  if [ -f "$LAUNCH" ]; then
    PREFLIGHT_ALLOW_HEAVY=1 bash "$LAUNCH" "$SMALL_CEILING_MB" "$L" "$name" "$@" > /dev/null 2>&1
    local e; e=$(grep '^exit=' "$L/$name.watch" | tail -1 | sed 's/exit=\([0-9]*\).*/\1/')
    grep -q "WATCHDOG KILL" "$L/$name.watch" && { echo "WATCHDOG KILL in $name"; return 99; }
    return "${e:-98}"
  else "$@" > "$L/$name.out" 2> "$L/$name.err"; return $?; fi
}
# reference hashes: manifest path -> sha ; intermediate blobs -> MANIFEST_v3r (basename -> sha)
awk -F'\t' 'NR>1{print $3 "\t" $4}' "$HERE/MANIFEST.tsv" > "$WORK/ref_manifest.tsv"
awk '{n=$2; sub(/.*\//,"",n); print n "\t" $1}' "$IN/MANIFEST_v3r.sha256" > "$WORK/ref_v3r.tsv"
compare_dir() { # LABEL DIR PREFIX(path prefix in the manifest, e.g. LRSpectrumFull/L5S4) [v3r]   : compare every *.lean under DIR (non-recursive unless PREFIX ends with /...)
  local label=$1 dir=$2 prefix=$3 refmode=${4:-manifest}
  local out; out=$(cd "$dir" && find . -type f -name '*.lean' | sed 's|^\./||' | LC_ALL=C sort | while IFS= read -r f; do shasum -a 256 "$f"; done)
  local r
  if [ "$refmode" = v3r ]; then
    r=$(printf '%s\n' "$out" | awk -v refF="$WORK/ref_v3r.tsv" 'BEGIN{while((getline l<refF)>0){split(l,a,"\t"); ref[a[1]]=a[2]}} NF==2{n=$2; sub(/.*\//,"",n); if(!(n in ref)) {nr++; next} if(ref[n]==$1) s++; else {d++; print "DIFFERENT " $2 > "/dev/stderr"}} END{printf "%d %d %d\n", s+0, d+0, nr+0}')
  else
    r=$(printf '%s\n' "$out" | awk -v pre="$prefix" -v refF="$WORK/ref_manifest.tsv" 'BEGIN{while((getline l<refF)>0){split(l,a,"\t"); ref[a[1]]=a[2]}} NF==2{p=pre "/" $2; if(!(p in ref)) {nr++; next} if(ref[p]==$1) s++; else {d++; print "DIFFERENT " p > "/dev/stderr"}} END{printf "%d %d %d\n", s+0, d+0, nr+0}')
  fi
  local s d nr; read -r s d nr <<< "$r"
  NSAME=$((NSAME+s)); NDIFF=$((NDIFF+d)); NNOREF=$((NNOREF+nr))
  echo "COMPARE $label: identical $s, different $d, not in reference $nr"
}
install_dir() { # DIR PREFIX : copy files whose sha256 equals the manifest into LEAN_DIR, only where absent
  local dir=$1 prefix=$2 f p n=0
  for f in "$dir"/*.lean; do [ -f "$f" ] || continue
    p="$prefix/$(basename "$f")"; mkdir -p "$LEAN_DIR/$prefix"
    if grep -q "^$p	$(shasum -a 256 "$f" | cut -d' ' -f1)\$" "$WORK/ref_manifest.tsv" && [ ! -e "$LEAN_DIR/$p" ]; then cp "$f" "$LEAN_DIR/$p"; n=$((n+1)); fi
  done; echo "installed $n files into $LEAN_DIR/$prefix"
}
T0=$(date +%s)
echo "mode $MODE, steps $STEPS, LEAN_DIR $LEAN_DIR"

# ---- patched copies of generators that hard-code the placeholder path prefix /DEV_TREE ---------------------------------------------------------------
patch_copy() { # CRATE_DIR_NAME (relative to generators/) : copy to work/patched/<name> with the paths redirected
  local c=$1 d=$WORK/patched/$1
  rm -rf "${WORK:?}/patched/${c:?}"; mkdir -p "$d"; rsync -a "$GEN/$c/" "$d/"
  [ -d "$GEN/lean5_wp0a" ] && { mkdir -p "$WORK/patched/lean5_wp0a"; rsync -a "$GEN/lean5_wp0a/" "$WORK/patched/lean5_wp0a/"; }
}
VIEW=$WORK/view          # lean view for agg / hl: L5S4, L5Reg and .lake are symlinks to LEAN_DIR (read only); AggFive and L5S5 are real, empty directories
VIEWR=$WORK/viewreg      # view for l5reg: L5S4 and .lake symlinks, L5Reg a real empty directory that receives Reg<rep>.lean and Mem.lean
make_view() {
  rm -rf "${VIEW:?}" "${VIEWR:?}"; mkdir -p "$VIEW/LRSpectrumFull/L5S5" "$VIEW/state_agg" "$VIEW/state_hl" "$VIEWR/LRSpectrumFull/L5Reg"
  ln -s "$LEAN_DIR/.lake" "$VIEW/.lake"; ln -s "$LEAN_DIR/LRSpectrumFull/L5S4" "$VIEW/LRSpectrumFull/L5S4"; ln -s "$LEAN_DIR/LRSpectrumFull/L5Reg" "$VIEW/LRSpectrumFull/L5Reg"
  ln -s "$LEAN_DIR/.lake" "$VIEWR/.lake"; ln -s "$LEAN_DIR/LRSpectrumFull/L5S4" "$VIEWR/LRSpectrumFull/L5S4"
  cp "$IN/extra_built.txt" "$VIEW/state_agg/extra_built.txt"
}
# ---- build ---------------------------------------------------------------------------------------------------------------------------------
if step build; then
  patch_copy l5s4o_named; patch_copy l5_reg; patch_copy l5_agg; patch_copy l5_hlines
  MODN=$IN/modname.tsv; PLAN=$IN/plan.tsv
  sed -i '' "s#/DEV_TREE/work/l5_rollout/modname.tsv#$MODN#" "$WORK/patched/l5s4o_named/src/main.rs"
  sed -i '' "s#const LEAN: &str = \"[^\"]*\"#const LEAN: \&str = \"$VIEWR/LRSpectrumFull\"#; s#const BUILD: &str = \"[^\"]*\"#const BUILD: \&str = \"$VIEWR/.lake/build/lib/lean/LRSpectrumFull\"#; s#const PLAN: &str = \"[^\"]*\"#const PLAN: \&str = \"$PLAN\"#" "$WORK/patched/l5_reg/src/main.rs"
  sed -i '' "s#const LEAN: &str = \"[^\"]*\"#const LEAN: \&str = \"$VIEW/LRSpectrumFull\"#; s#const BUILD: &str = \"[^\"]*\"#const BUILD: \&str = \"$VIEW/.lake/build/lib/lean/LRSpectrumFull\"#; s#const STATE: &str = \"[^\"]*\"#const STATE: \&str = \"$VIEW/state_hl\"#" "$WORK/patched/l5_hlines/src/main.rs"
  sed -i '' "s#/DEV_TREE/work/l5_rollout/modname.tsv#$MODN#; s#/DEV_TREE/work/l5_agg/state#$VIEW/state_agg#g" "$WORK/patched/l5_agg/src/gen.rs"
  for p in "lean5_data/gen3:$GEN/lean5_data/gen3" "l5s4o:$WORK/patched/l5s4o_named" "l5qemit:$GEN/l5_lines_driver/emit" "l5reg:$WORK/patched/l5_reg" "l5_agg:$WORK/patched/l5_agg" "l5hlines:$WORK/patched/l5_hlines"; do
    n=${p%%:*}; d=${p#*:}
    small "build_$(echo "$n" | tr / _)" cargo build --release --offline --manifest-path "$d/Cargo.toml" || { echo "BUILD FAILED $n (see $L/build_$(echo "$n" | tr / _).err)"; exit 1; }
  done
  # the patched copies live in work/patched, the lean5_wp0a path dependency of l5s4o_named resolves to work/patched/lean5_wp0a
  echo "built generators in $(( $(date +%s) - T0 )) s"
fi
for b in l5v3 l5s4o l5qemit l5reg l5_agg l5hlines; do [ -x "$BIN/$b" ] || echo "note: $BIN/$b missing (step build not run?)"; done

# ---- v3 + s4o ---------------------------------------------------------------------------------------------------------------------------------
run_reps() { # LABEL REPLIST(space separated) : l5v3 emit+v3 for the reps, then l5s4o per rep; compare
  local label=$1 reps0=$2 reps="" ids r0
  for r0 in $reps0; do case "$SKIP_REPS" in *" $r0 "*) echo "skip rep $r0 (DONE_PRIOR in the rollout; not produced by this chain)" ;; *) reps="$reps $r0" ;; esac; done
  [ -n "$reps" ] || return 0
  ids=$(echo $reps | tr ' ' ',')
  local D=$WORK/v3_$label O=$WORK/o_$label
  rm -rf "${D:?}" "${O:?}"; mkdir -p "$D" "$D/log" "$O" "$WORK/tsv_$label"
  export L5D_SRC=$D L5D_LOG=$D/log L5V3_PR=300 L5V3_LAYOUT=A
  small "emit_$label" "$BIN/l5v3" emit "$ids" 1700 || { echo "l5v3 emit failed ($label)"; return 1; }
  small "v3_$label" "$BIN/l5v3" v3 "$ids" 1700 || { echo "l5v3 v3 failed ($label)"; return 1; }
  unset L5D_SRC L5D_LOG L5V3_PR L5V3_LAYOUT
  local r tags j f
  # as in rollout/rep_run.sh step 1: the node-side modules are already in the output directory when l5s4o runs (it adds `import ...GD3N<rep>Z` iff that file exists there)
  for f in "$D"/GD3N*.lean "$D"/GD3F2N*.lean; do [ -f "$f" ] && cp "$f" "$O/"; done
  for r in $reps; do
    tags=""
    # numeric chunk order (as rep_run.sh: `sort -n`): the class numbering of l5s4o depends on the order of the tags
    for j in $(ls "$D" | grep -E "^GD3F2L${r}R[0-9]+\.lean$" | sed -E 's/.*R([0-9]+)\.lean/\1/' | sort -n); do tags="$tags c$j=$D/GD3F2L${r}R$j.lean"; done
    small "s4o_$r" "$BIN/l5s4o" "$r" "$O" "$WORK/tsv_$label" $tags || { echo "l5s4o failed rep $r (see $L/s4o_$r.err)"; return 1; }
  done
  for f in "$D"/GD3N*.lean "$D"/GD3F2N*.lean; do [ -f "$f" ] && rm -f "${O:?}/$(basename "$f")"; done   # keep only the l5s4o outputs in $O
  # v3 outputs: GD3N*, GD3F2N* are tree modules (manifest); GD3F2L* are intermediate blobs (MANIFEST_v3r)
  mkdir -p "$D/tree" "$D/blobs"
  for f in "$D"/GD3N*.lean "$D"/GD3F2N*.lean; do [ -f "$f" ] && mv "$f" "$D/tree/"; done
  for f in "$D"/GD3F2L*.lean; do [ -f "$f" ] && mv "$f" "$D/blobs/"; done
  compare_dir "$label v3 node modules GD3N*/GD3F2N* (manifest)" "$D/tree" LRSpectrumFull/L5S4
  compare_dir "$label v3 blobs GD3F2L* (MANIFEST_v3r)" "$D/blobs" - v3r
  compare_dir "$label l5s4o modules GD3O* (manifest)" "$O" LRSpectrumFull/L5S4
  [ "$INSTALL" = 1 ] && { install_dir "$D/tree" LRSpectrumFull/L5S4; install_dir "$O" LRSpectrumFull/L5S4; }
  [ "$KEEP" = 1 ] || rm -rf "${D:?}" "${O:?}" "${WORK:?}/tsv_$label"
}
if step v3 || step s4o; then
  if [ "$MODE" = sample ]; then run_reps sample "$SAMPLE_REPS"
  else
    b=0; while [ $((b*50)) -lt $NREP ]; do
      reps=""; for r in $(seq $((b*50)) $((b*50+49))); do [ "$r" -lt $NREP ] || break; reps="$reps $r"; done
      run_reps "b$b" "$reps" || exit 1; b=$((b+1))
    done
  fi
fi

# ---- lines ---------------------------------------------------------------------------------------------------------------------------------------
LINTL=$LEAN_DIR/LRSpectrumFull/L5S4/LinTL.lean
if step lines; then
  slices=""
  if [ "$MODE" = sample ]; then slices=$LINES_SLICES; else lo=0; while [ $lo -lt "$PLANN" ]; do hi=$((lo+50)); [ $hi -gt "$PLANN" ] && hi=$PLANN; slices="$slices $lo:$hi"; lo=$hi; done; fi
  for sl in $slices; do
    lo=${sl%%:*}; hi=${sl#*:}; D=$WORK/lines_$lo
    rm -rf "${D:?}"; mkdir -p "$D"
    small "emitc_$lo" "$BIN/l5qemit" emitc "$IN/src_t4_all" "$IN/t4_classes.tsv" "$LINTL" all "$IN/plan.tsv" "$D" "$lo" "$hi" || { echo "l5qemit failed slice $sl (see $L/emitc_$lo.err)"; exit 1; }
    grep -q 'interpreter rejected 0' "$L/emitc_$lo.err" || { echo "interpreter of the emitter rejected a class in slice $sl"; exit 1; }
    compare_dir "lines plan[$lo,$hi) LinRQSC*" "$D" LRSpectrumFull/L5S4
    [ "$INSTALL" = 1 ] && install_dir "$D" LRSpectrumFull/L5S4
    [ "$KEEP" = 1 ] || rm -rf "${D:?}"
  done
fi

# ---- reg / agg / hl (need a lean tree; write only under work/view) ----------------------------------------------------------------------
if step reg || step agg || step hl; then make_view; fi
if step reg; then
  FORCE=1 small gen_reg "$BIN/l5reg" gen $REG_REPS; FORCE=1 small gen_mem "$BIN/l5reg" mem
  compare_dir "l5reg Reg<rep> and Mem (reps $REG_REPS)" "$VIEWR/LRSpectrumFull/L5Reg" LRSpectrumFull/L5Reg
fi
if step agg; then
  small gen_agg "$BIN/l5_agg" gen "$VIEW" "$IN/rollout_results.tsv" "$IN/T2RL_STATUS.tsv" || { echo "l5_agg gen failed (see $L/gen_agg.err)"; exit 1; }
  compare_dir "l5_agg AggFive (all)" "$VIEW/LRSpectrumFull/AggFive" LRSpectrumFull/AggFive
  compare_dir "l5_agg L5S5/FiveSpeedFinal" "$VIEW/LRSpectrumFull/L5S5" LRSpectrumFull/L5S5
fi
if step hl; then
  mkdir -p "$VIEW/LRSpectrumFull/AggFive/Hl"
  small gen_hl "$BIN/l5hlines" gen || { echo "l5hlines gen failed (see $L/gen_hl.err)"; exit 1; }
  compare_dir "l5hlines AggFive/Hl (all)" "$VIEW/LRSpectrumFull/AggFive/Hl" LRSpectrumFull/AggFive/Hl
fi
echo "regeneration summary: $NSAME files identical, $NDIFF different, $NNOREF without a reference hash; total $(( $(date +%s) - T0 )) s"
[ "$KEEP" = 1 ] || { rm -rf "${WORK:?}/target" "${WORK:?}/patched" "${VIEW:?}" "${VIEWR:?}" "${WORK:?}/ref_manifest.tsv" "${WORK:?}/ref_v3r.tsv"; }
[ "$NDIFF" = 0 ] && [ "$NSAME" -gt 0 ]
