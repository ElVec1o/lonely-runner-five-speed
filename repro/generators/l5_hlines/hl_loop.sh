#!/bin/bash
# hl_loop.sh : repeat hl_build.sh until a full pass finds nothing to build and nothing blocked (the agg loop keeps regenerating/rebuilding AggFive modules).  Stop: l5_hlines/STOP.  Max 6 h.
P=/DEV_TREE
D=$P/work/l5_hlines
LD=$P/logs/l5hl
T0=$(date +%s)
while [ $(( $(date +%s) - T0 )) -lt 21600 ]; do
  [ -f $D/STOP ] && { echo "$(date +%T) STOP" >> $LD/hl_loop.log; exit 0; }
  : > $LD/hl_blocked.log
  bash $D/hl_build.sh >> $LD/pipe3.log 2>&1
  NB=$(grep -c . $LD/hl_blocked.log)
  LAST=$(grep "level" $LD/hl_build.log | tail -4 | awk '{b+=$5} END{print b+0}')
  echo "$(date +%T) pass done: blocked entries $NB, built-this-pass $LAST" >> $LD/hl_loop.log
  if [ "$NB" = 0 ] && [ "$LAST" = 0 ]; then echo "$(date +%T) converged" >> $LD/hl_loop.log; exit 0; fi
  sleep 120
done
