#!/bin/bash
# driver.sh : RESUMABLE build driver of the five-speed lines certificate (1,063 chunk modules + assemblies + LinRAll + LinRCov/LinRFinal), lane 1.
#   one process (pidfile); order.txt = cheap nodes first, node 5 last, inside a node the lightest chunks first; per-module atomic claim (mkdir claims/MOD);
#   per-module state row state/MOD.row (atomic mv) -> results.tsv (regen.sh); skips modules whose row is DONE;
#   chunk sources are emitted LAZILY (emit_all.sh B B for the batch of the module) and copied into the lean tree;
#   STOP file after 3 consecutive real errors (build errors, not guard kills), or when disk < 5 GB for 30 min (disk_gate);
#   builds through build_mod.sh (lane lock shared with l5_rollout, guard gate, own 9 GB tree-RSS killer, one-off wrapper ceiling 12000).
# Resume = run it again (claims of unfinished modules are cleared).  Stop = touch STOP (finishes the current module, then halts).
. /DEV_TREE/work/l5_lines_driver/common.sh
if [ -f $RO/driver.pid ] && kill -0 $(cat $RO/driver.pid) 2>/dev/null; then echo "driver already running pid $(cat $RO/driver.pid)"; exit 1; fi
echo $$ > $RO/driver.pid
trap 'rm -f $RO/driver.pid; elog "driver exit"' EXIT
mkdir -p $RO/state $RO/claims $RO/logs/mod
rm -f $RO/STOP
for c in $RO/claims/*; do [ -d "$c" ] || continue; r=$(basename $c); grep -qE "	(DONE)	" $RO/state/$r.row 2>/dev/null || rmdir $c; done
elog "driver start pid $$"
ERR=0
while IFS=$'\t' read -r idx mod kind node pts; do
  [ -f $RO/STOP ] && { elog "STOP seen: halting"; break; }
  [ -z "$mod" ] && continue
  grep -qE "	DONE	" $RO/state/$mod.row 2>/dev/null && continue
  mkdir $RO/claims/$mod 2>/dev/null || continue
  disk_gate || break
  START=$(now); T0=$(date +%s)
  row() {   # row STATUS AXIOMS NOTE
    local agg=$(awk -F'\t' -v m=$mod '$3==m && $4=="OK"{c=$6; p=$7; if($8>p)p=$8} $3==m && $4=="KILL"{k++} END{printf "%.1f\t%d\t%d", c, p, k}' $RO/modules.tsv)
    printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$idx" "$mod" "$kind" "$node" "$pts" "$1" "$agg" "$(( $(date +%s) - T0 ))" "$2" "$START" "$(now)" "$3" > $RO/state/$mod.row.tmp && mv $RO/state/$mod.row.tmp $RO/state/$mod.row
    bash $RO/regen.sh; }
  # ---- source: lazy emission + copy into the lean tree
  case $kind in
    chunk) B=$(( $(awk -F'\t' -v m=$mod '$1==m{print $6}' $PLAN) / BATCH ))
           bash $RO/emit_all.sh $B $B > $RO/logs/emit/last_emit.txt 2>&1; ERC=$?
           [ $ERC -ne 0 ] && { row FAILED - "emit rc=$ERC: $(tail -c 200 $RO/logs/emit/last_emit.txt | tr '\n\t' '  ')"; echo "emit failure rc=$ERC (module $mod)" > $RO/STOP; elog "STOP: emit rc=$ERC"; rmdir $RO/claims/$mod; break; }
           SRCF=$SRCC/batch_$(printf %04d $B)/$mod.lean;;
    asm) SRCF=$RO/src_asm/$mod.lean;;
    *) SRCF="";;
  esac
  if [ -n "$SRCF" ]; then
    [ -f "$SRCF" ] || { row FAILED - "source $SRCF missing"; rmdir $RO/claims/$mod; ERR=$((ERR+1)); [ $ERR -ge 3 ] && break; continue; }
    cmp -s $SRCF $L5/$mod.lean || cp $SRCF $L5/$mod.lean
  fi
  [ -f $L5/$mod.lean ] || { row FAILED - "no lean source $mod"; rmdir $RO/claims/$mod; continue; }
  row RUNNING - "started"
  bash $RO/build_mod.sh $mod $kind; rc=$?
  elog "module $mod rc=$rc"
  case $kind in cov) ANAME="Lin.lines_clause_tab";; final) ANAME="Lin.lines_clause_all";; *) ANAME="$mod.ok";; esac
  case $rc in
    0) AXR=$(bash $RO/axcheck.sh $RO/logs/mod/$mod.out $ANAME); AXRC=$?
       if [ $AXRC -eq 0 ]; then row DONE "$AXR" ok; ERR=0
       else row FAILED "$AXR" "axiom check did not return STD"; ERR=$((ERR+1)); rmdir $RO/claims/$mod; fi;;
    10) row FAILED - "real build error: $(grep -m2 -E 'error' $RO/logs/mod/$mod.out | cut -c1-160 | tr '\n\t' '  ')"; ERR=$((ERR+1)); rmdir $RO/claims/$mod;;
    11) row FAILED - "guard/watchdog kills exhausted (6 retries)"; rmdir $RO/claims/$mod;;
    13) row FAILED - "lane wait timeout"; rmdir $RO/claims/$mod;;
    3)  row BLOCKED - "an import is not built"; rmdir $RO/claims/$mod;;
    14|20) row STOPPED - "disk/STOP"; rmdir $RO/claims/$mod; break;;
    *) row FAILED - "infrastructure rc=$rc"; rmdir $RO/claims/$mod; ERR=$((ERR+1));;
  esac
  if [ $ERR -ge 3 ]; then echo "3 consecutive real errors (last module $mod)" > $RO/STOP; elog "STOP written: 3 consecutive real errors"; break; fi
done < $RO/order.txt
elog "driver loop end"
