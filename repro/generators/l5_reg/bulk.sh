#!/bin/bash
# bulk.sh : build every L5Reg.Reg<c> listed in reps_all.txt (except those already built), batches of 40 through lane_reg.sh (lane 1, wrapper 12000 MB).
# Stop file: work/l5_reg/STOP (checked between batches).  Stops at the first failed batch.
D=/DEV_TREE/work/l5_reg
LD=/DEV_TREE/logs/l5reg
OL=/DEV_TREE/lean/.lake/build/lib/lean/LRSpectrumFull/L5Reg
LS=/DEV_TREE/lean/LRSpectrumFull/L5Reg
: > $LD/bulk_todo.txt
for c in $(cat $LD/reps_all.txt); do
  [ "$c" = 304 ] && continue; [ "$c" = 265 ] && continue
  if [ -f $OL/Reg$c.olean ] && [ ! $LS/Reg$c.lean -nt $OL/Reg$c.olean ]; then continue; fi
  echo L5Reg.Reg$c >> $LD/bulk_todo.txt
done
echo "todo $(wc -l < $LD/bulk_todo.txt) $(date +%T)" >> $LD/bulk.log
split -l 40 $LD/bulk_todo.txt $LD/bulk_batch_
for f in $LD/bulk_batch_*; do
  [ -f $D/STOP ] && { echo "STOP file, ending $(date +%T)" >> $LD/bulk.log; exit 0; }
  bash $D/lane_reg.sh $(cat $f) >> $LD/bulk_lane.log 2>&1
  rc=$?
  echo "batch $(basename $f) rc=$rc $(date +%T)" >> $LD/bulk.log
  [ $rc -ne 0 ] && { echo "FAILED batch $f, stopping" >> $LD/bulk.log; exit $rc; }
done
echo "all done $(date +%T)" >> $LD/bulk.log
