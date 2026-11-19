#!/bin/bash
# usage: lane.sh MODULE [MODULE...]    (MODULE = dotted name under LRSpectrumFull, e.g. L5S5.AggBlock or AggFive.Clean.T2D3)
# Lane 1 (LEAN_SLOT.lock, shared with the rep #304/#265 chains). Waits for the lock (poll 1 s, up to 3 h), takes it ONCE per batch,
# then per module: disk gate >= 5 GB, guard gate (total lean RSS + 4.0 GB <= guard limit - 1.5 GB), one-off wrapper 12000 MB
# (watchdog kills the process tree at 90 percent), lake build of ONE module whose imports are built (checked by the caller).
# On a guard/watchdog kill: log, wait 10 min, retry up to 6 times. Stops at the first failed module. Never removes a lock it did not create.
LOCK=/DEV_TREE/logs/LEAN_SLOT.lock
LD=/DEV_TREE/logs/l5agg
GL=/DEV_TREE/guard.log
mkdir -p "$LD"
LIM=$(grep 'guard started, limit' "$GL" | tail -1 | sed 's/.*limit \([0-9.]*\) GB.*/\1/'); LIM=${LIM:-20}
NEED=$(awk -v l="$LIM" 'BEGIN{printf "%d", (l-1.5-4.0)*1048576}')
gate() {
  DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  FRK=$(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%d", s}')
  if [ "$DG" -lt 3 ] || [ "${FRK:-0}" -gt "$NEED" ]; then echo "GATE FAIL disk=${DG}GB leanRSS_KB=${FRK} need_le=${NEED}"; return 1; fi
  return 0
}
T0=$(date +%s); GOT=0
while [ $(( $(date +%s) - T0 )) -lt 10800 ]; do
  if mkdir "$LOCK" 2>/dev/null; then GOT=1; break; fi
  sleep 0.01
done
[ "$GOT" = 1 ] || { echo "LOCK TIMEOUT"; exit 9; }
trap 'rmdir "$LOCK" 2>/dev/null' EXIT
echo "lock taken lim=${LIM} $(date +%T)"
rc=0
for M in "$@"; do
  NAME=$(echo "$M" | tr '.' '_')
  TRY=0
  while :; do
    TRY=$((TRY+1))
    G=0; while :; do gate && break; G=$((G+1)); [ $G -gt 30 ] && { echo "GATE giving up before $M"; rc=5; break 2; }; sleep 60; done
    echo "build $M try $TRY $(date +%T)"
    rm -f "$LD/$NAME.out" "$LD/$NAME.watch"
    bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 12000 "$LD" "$NAME" bash -c "cd /DEV_TREE/lean && exec /usr/bin/time -l lake build LRSpectrumFull.$M"
    if grep -q "Build completed successfully" "$LD/$NAME.out" 2>/dev/null; then echo "done $M $(date +%T)"; break; fi
    if grep -q "WATCHDOG KILL" "$LD/$NAME.watch" 2>/dev/null && [ $TRY -lt 6 ]; then echo "killed $M, waiting 10 min"; sleep 600; continue; fi
    echo "FAILED $M"; rc=1; break 2
  done
done
exit $rc
