#!/bin/bash
# build_all.sh : resumable, incremental builder of the generated aggregation (lane 1, via lane2.sh).  usage: nohup bash build_all.sh [BATCH] &
# Each round: ask `l5_agg pending` for the modules whose olean is missing/stale (dependency order), take the first BATCH (default 10), build them with
# ONE lock acquisition (lane2.sh), repeat.  Stops at the first failed module (log: logs/l5agg/build_all.log) or when `state/STOP` exists.
# Re-run it after `l5_agg gen` (the rollout adds reps); only regenerated modules and their ancestors are pending.
A=/DEV_TREE/work/l5_agg
L=/DEV_TREE/lean
LOG=/DEV_TREE/logs/l5agg/build_all.log
BATCH=${1:-10}
echo "build_all start $(date +%T) pid $$ batch $BATCH" >> "$LOG"
echo $$ > "$A/state/build_all.pid"
while :; do
  [ -f "$A/state/STOP" ] && { echo "STOP file, exit $(date +%T)" >> "$LOG"; break; }
  PEND=$("$A/target/release/l5_agg" pending "$L" | head -n "$BATCH" | tr '\n' ' ')
  [ -z "$PEND" ] && { echo "ALL BUILT $(date +%T)" >> "$LOG"; break; }
  echo "round: $PEND" >> "$LOG"
  bash "$A/lane2.sh" $PEND >> "$LOG" 2>&1 || { echo "ROUND FAILED $(date +%T)" >> "$LOG"; break; }
done
rm -f "$A/state/build_all.pid"
