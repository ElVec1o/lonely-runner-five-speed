#!/bin/bash
# reg_new.sh : build every L5Reg.Reg<c> whose source exists and whose olean is missing/stale (all reps, 265/304 included), batches of 40 through lane_reg.sh (lane 1, wrapper 12000 MB).
# Stop file: l5_reg/STOP.  Log: logs/l5reg/reg_new.log
D=/DEV_TREE/work/l5_reg
LD=/DEV_TREE/logs/l5reg
OL=/DEV_TREE/lean/.lake/build/lib/lean/LRSpectrumFull/L5Reg
LS=/DEV_TREE/lean/LRSpectrumFull/L5Reg
: > $LD/reg_new_todo.txt
for f in $LS/Reg[0-9]*.lean; do
  b=$(basename $f .lean)
  if [ -f $OL/$b.olean ] && [ ! $f -nt $OL/$b.olean ]; then continue; fi
  echo L5Reg.$b >> $LD/reg_new_todo.txt
done
echo "todo $(wc -l < $LD/reg_new_todo.txt) $(date +%T)" >> $LD/reg_new.log
rm -f $LD/reg_new_batch_*
split -l 40 $LD/reg_new_todo.txt $LD/reg_new_batch_
for f in $LD/reg_new_batch_*; do
  [ -f $D/STOP ] && { echo "STOP file, ending $(date +%T)" >> $LD/reg_new.log; exit 0; }
  bash $D/lane_reg.sh $(cat $f) >> $LD/reg_new_lane.log 2>&1
  rc=$?
  echo "batch $(basename $f) rc=$rc $(date +%T)" >> $LD/reg_new.log
  [ $rc -ne 0 ] && { echo "FAILED batch $f, stopping" >> $LD/reg_new.log; exit $rc; }
done
echo "all done $(date +%T)" >> $LD/reg_new.log
