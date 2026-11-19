#!/bin/bash
# lean_check.sh LABEL FILE.lean : `lake env lean FILE` (elaborate, no olean written) under the lane-1 lock; memory gate only (read-only run).
# Output: logs/l5agg/meas/check_<LABEL>.out/.err/.watch.  Used for the aggregation controls when the 5 GB disk gate blocks module builds.
L=/DEV_TREE/lean
LD=/DEV_TREE/logs/l5agg/meas
LOCK=/DEV_TREE/logs/LEAN_SLOT.lock
GL=/DEV_TREE/guard.log
LABEL=$1; F=$2
mkdir -p "$LD"
LIM=$(grep 'guard started, limit' "$GL" | tail -1 | sed 's/.*limit \([0-9.]*\) GB.*/\1/'); LIM=${LIM:-20}
NEED=$(awk -v l="$LIM" 'BEGIN{printf "%d", (l-1.5-4.0)*1048576}')
T0=$(date +%s); GOT=0
while [ $(( $(date +%s) - T0 )) -lt 10800 ]; do mkdir "$LOCK" 2>/dev/null && { GOT=1; break; }; sleep 0.01; done
[ "$GOT" = 1 ] || { echo "LOCK TIMEOUT"; exit 9; }
trap 'rmdir "$LOCK" 2>/dev/null' EXIT
FRK=$(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%d", s}')
[ "${FRK:-0}" -le "$NEED" ] || { echo "GATE FAIL mem"; exit 5; }
bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 12000 "$LD" "check_$LABEL" bash -c "cd $L && exec /usr/bin/time -l lake env lean $F"
echo "exit done $LABEL"
