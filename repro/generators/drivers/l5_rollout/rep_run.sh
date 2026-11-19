#!/bin/bash
# rep_run.sh REP : the full pipeline of one depth-2 representative.
#   1 copy the node-side modules (GD3N<rep>, M*, Z, GD3F2N<rep>) of the v3 generator into the lean tree (never overwrite a differing existing file)
#   2 run l5s4o (real class maps, local class table, chunk modules, main module t3_nodeU) into the lean tree
#   3 build the import closure bottom-up, one module at a time (build_mod.sh), skipping modules whose olean is current
#   4 #print axioms check of t3_nodeU (standard axioms only), cleanup of the self-class input blobs
# state row: state/<rep>.row (one line, atomic), fields as in results.tsv.  exit: 0 DONE, 10 real error, 11 kills exhausted, 20 STOP, 14 disk, other = infrastructure
. /DEV_TREE/work/l5_rollout/common.sh
REP=$1
B=$((REP/50)); SRC=$DATA/batch_$(printf %04d $B)
T0=$(date +%s); START=$(now)
LEAVES=$(awk -F'\t' -v r=$REP '$1==r{print $3}' $RO/order.txt); CH=$(awk -F'\t' -v r=$REP '$1==r{print $4}' $RO/order.txt); NM=$(awk -F'\t' -v r=$REP '$1==r{print $5}' $RO/order.txt)
MAIN=$(main_of $REP)   # main-module name (modname.tsv; default GD3O<rep>)

row() {   # row STATUS AXIOMS NOTE
  local st=$1 ax=$2 note=$3
  local agg=$(awk -F'\t' -v r=$REP '$2==r && $4=="OK"{n++; c+=$6; if($7>p)p=$7; if($8>p)p=$8} $2==r && $4=="KILL"{k++} END{printf "%d\t%.1f\t%d\t%d", n, c, p, k}' $RO/modules.tsv)
  local w=$(( $(date +%s) - T0 ))
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$REP" "$st" "${LEAVES:-0}" "${CH:-0}" "${NM:-0}" "$agg" "$w" "$ax" "$START" "$(now)" "$note" > $RO/state/$REP.row.tmp && mv $RO/state/$REP.row.tmp $RO/state/$REP.row
  bash $RO/regen.sh
}

row RUNNING - "started"
disk_gate || { row STOPPED - "disk gate"; exit 14; }

# ---- 1. node-side modules
for f in $SRC/GD3N$REP.lean $SRC/GD3N${REP}M[0-9]*.lean $SRC/GD3N${REP}Z.lean $SRC/GD3F2N$REP.lean; do
  [ -f "$f" ] || continue
  b=$(basename $f)
  if [ -f $L5/$b ]; then cmp -s $f $L5/$b || { elog "rep $REP: $b DIFFERS from the existing lean-tree file; existing file kept"; NOTE_DIFF="$NOTE_DIFF $b"; }
  else cp $f $L5/$b; fi
done
[ -f $L5/GD3F2N$REP.lean ] && [ -f $L5/GD3N$REP.lean ] || { row FAILED - "node-side sources missing in batch dir"; exit 12; }

# ---- 2. l5s4o
if [ ! -f $OLEAN/$MAIN.olean ]; then
  rm -f $L5/$MAIN.lean $L5/GD3O${REP}T.lean $L5/GD3O${REP}R*.lean
fi
TAGS=""
for j in $(ls $SRC | grep -E "^GD3F2L${REP}R[0-9]+\.lean$" | sed -E 's/.*R([0-9]+)\.lean/\1/' | sort -n); do TAGS="$TAGS c$j=$SRC/GD3F2L${REP}R$j.lean"; done
mkdir -p $RO/tsv $RO/logs/gen
if [ ! -f $L5/$MAIN.lean ]; then
  bash $LAUNCH_SMALL 790 $RO/logs/gen GEN$REP $L5S4O $REP $L5 $RO/tsv $TAGS
  grep -q '^exit=0' $RO/logs/gen/GEN$REP.watch && [ -f $L5/$MAIN.lean ] || { row FAILED - "l5s4o failed: $(tail -c 300 $RO/logs/gen/GEN$REP.err | tr '\n\t' '  ')"; exit 10; }
fi

# guard: the main module must be a generated rep module, never an S4O library module that happens to carry the same name
grep -q 'theorem t3_nodeU_of' $L5/$MAIN.lean || { row FAILED - "main module $MAIN is not a generated rep module (name collision?)"; exit 12; }

# ---- 3. build closure
VIS=$RO/state/$REP.vis; : > $VIS
ensure() {
  local m=$1 imp rc
  grep -qx "$m" $VIS && return 0
  echo "$m" >> $VIS
  [ -f $L5/$m.lean ] || { elog "rep $REP: missing source $m"; return 5; }
  for imp in $(grep -E '^import LRSpectrumFull\.L5S4\.' $L5/$m.lean | sed 's/^import LRSpectrumFull\.L5S4\.//'); do
    ensure $imp; rc=$?; [ $rc -ne 0 ] && return $rc
  done
  if [ -f $OLEAN/$m.olean ] && [ ! $L5/$m.lean -nt $OLEAN/$m.olean ]; then return 0; fi
  bash $RO/build_mod.sh $m $REP; return $?
}
ensure $MAIN; RC=$?
rm -f $VIS
if [ $RC -ne 0 ]; then
  case $RC in
    10) row FAILED - "real error in a module (see logs/mod/*.out of rep $REP, last row of modules.tsv)${NOTE_DIFF:+; differs:$NOTE_DIFF}";;
    11) row FAILED - "guard/watchdog kills exhausted (6 retries)";;
    13) row FAILED - "lane wait timeout";;
    20) row STOPPED - "STOP file";;
    14) row STOPPED - "disk gate";;
    *)  row FAILED - "infrastructure rc=$RC";;
  esac
  exit $RC
fi

# ---- 4. axioms
AXF=$RO/logs/mod/$MAIN.out
if [ -f $AXF ] && [ $OLEAN/$MAIN.olean -nt $L5/$MAIN.lean ]; then AXR=$(bash $RO/axcheck.sh $AXF N$REP.t3_nodeU); AXRC=$?; else AXR="NOLINE"; AXRC=2; fi
if [ $AXRC -ne 0 ]; then
  # the main module may have been built earlier (out file replaced); re-observe with the module's own output if needed
  row FAILED "$AXR" "axiom check did not return STD${NOTE_DIFF:+; differs:$NOTE_DIFF}"; exit 10
fi
# cleanup of the self-class input blobs (regenerable, manifest MANIFEST_v3r.sha256)
rm -f $SRC/GD3F2L${REP}R*.lean $SRC/GD3F2L${REP}.lean
row DONE "$AXR" "ok${NOTE_DIFF:+; differs:$NOTE_DIFF}"
exit 0
