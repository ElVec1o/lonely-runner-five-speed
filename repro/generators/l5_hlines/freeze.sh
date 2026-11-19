#!/bin/bash
# freeze.sh : (S4V) take a consistent snapshot of the aggregation: wait for the agg loop to exit (LOOP_STOP written by hand), build every pending generated module (build_all.sh),
# wait for the hlines mirror to converge (hl_loop.sh), then build L5S5.FiveSpeedFinal and L5S5.FiveSpeedFinal2.  Log: logs/l5hl/freeze.log
P=/DEV_TREE
A=$P/work/l5_agg
D=$P/work/l5_hlines
LD=$P/logs/l5hl
OL=$P/lean/.lake/build/lib/lean/LRSpectrumFull
log() { echo "$(date +%T) $*" >> $LD/freeze.log; }
while [ -f $A/state/loop.pid ] && kill -0 "$(cat $A/state/loop.pid)" 2>/dev/null; do sleep 5; done
log "agg loop gone"
bash $A/build_all.sh 10 >> $LD/freeze_build_all.log 2>&1
log "build_all done: $(tail -1 $P/logs/l5agg/build_all.log)"
rm -f $D/STOP
T0=$(date +%s)
while [ $(( $(date +%s) - T0 )) -lt 7200 ]; do
  [ -f $OL/AggFive/Hl/Top.olean ] && [ ! $P/lean/LRSpectrumFull/AggFive/Hl/Top.lean -nt $OL/AggFive/Hl/Top.olean ] && break
  if ! pgrep -f hl_loop.sh > /dev/null; then bash $D/hl_loop.sh >> $LD/pipe3.log 2>&1; fi
  sleep 20
done
log "Hl.Top olean: $(ls $OL/AggFive/Hl/Top.olean 2>&1 | tail -c 40)"
bash $P/work/l5_reg/lane_reg.sh L5S5.FiveSpeedFinal L5S5.FiveSpeedFinal2 >> $LD/freeze_final.log 2>&1
log "final2 rc=$?"
