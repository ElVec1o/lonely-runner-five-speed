#!/bin/bash
# rollout.sh : the resumable driver. One process (pidfile), reps in order.txt (cost ascending), per-rep atomic claim (mkdir claims/<rep>),
# skips reps whose state row is DONE / DONE_PRIOR / BLOCKED, stops (STOP file) after 3 consecutive real errors on normal reps or on the disk rule.
# Resume = run it again (claims of unfinished reps are cleared at start).   Stop = touch STOP (finishes the current module, then halts).
. /DEV_TREE/work/l5_rollout/common.sh
if [ -f $RO/driver.pid ] && kill -0 $(cat $RO/driver.pid) 2>/dev/null; then echo "driver already running pid $(cat $RO/driver.pid)"; exit 1; fi
echo $$ > $RO/driver.pid
trap 'rm -f $RO/driver.pid; elog "driver exit"' EXIT
mkdir -p $RO/state $RO/claims $RO/logs
rm -f $RO/STOP
for c in $RO/claims/*; do [ -d "$c" ] || continue; r=$(basename $c); grep -qE "	(DONE|DONE_PRIOR|BLOCKED)	" $RO/state/$r.row 2>/dev/null || rmdir $c; done
elog "driver start pid $$"
ERR=0
while IFS=$'\t' read -r rep cost leaves chunks nm; do
  [ -f $RO/STOP ] && { elog "STOP seen: halting"; break; }
  [ -z "$rep" ] && continue
  grep -qE "	(DONE|DONE_PRIOR|BLOCKED)	" $RO/state/$rep.row 2>/dev/null && continue
  mkdir $RO/claims/$rep 2>/dev/null || continue
  disk_gate || break
  bash $RO/rep_run.sh $rep; rc=$?
  elog "rep $rep rc=$rc"
  case $rc in
    0) ERR=0;;
    10) if [ "$chunks" -le 12 ]; then ERR=$((ERR+1)); fi;;   # reps with more than 12 chunks (the 17+ big ones) may hit the flat-main limit: not counted
    11) ;;                                                   # guard kills exhausted: logged, not a real error
    20|14) break;;
    *) ERR=$((ERR+1));;
  esac
  [ $rc -ne 0 ] && rmdir $RO/claims/$rep 2>/dev/null
  if [ $ERR -ge 3 ]; then echo "3 consecutive real errors (last rep $rep)" > $RO/STOP; elog "STOP written: 3 consecutive real errors"; break; fi
done < $RO/order.txt
elog "driver loop end"
