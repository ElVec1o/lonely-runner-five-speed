#!/bin/bash
# usage: lane2.sh MODULE [MODULE...]   (dotted names under LRSpectrumFull)
# Like lane.sh, but the disk/guard gate is waited for OUTSIDE the lane lock (poll 3 s, up to 3 h): a gate failure releases lane 1 instead of
# holding it.  The lock (10 ms poll) is kept across the modules of one batch while the gate stays open.  Releases only a lock this script created.
# On a watchdog/guard kill: release, wait 10 min, retry up to 6 times.  Stops at the first failed module.
LOCK=/DEV_TREE/logs/LEAN_SLOT.lock
LD=/DEV_TREE/logs/l5reg
GL=/DEV_TREE/guard.log
mkdir -p "$LD"
LIM=$(grep 'guard started, limit' "$GL" | tail -1 | sed 's/.*limit \([0-9.]*\) GB.*/\1/'); LIM=${LIM:-20}
NEED=$(awk -v l="$LIM" 'BEGIN{printf "%d", (l-1.5-4.0)*1048576}')
gate() {
  DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  FRK=$(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%d", s}')
  [ "$DG" -ge 5 ] && [ "${FRK:-0}" -le "$NEED" ]
}
HELD=0
trap '[ "$HELD" = 1 ] && rmdir "$LOCK" 2>/dev/null' EXIT
acquire() {   # returns 0 with the lock held and the gate open
  if [ "$HELD" = 1 ]; then
    if gate; then return 0; fi
    rmdir "$LOCK" 2>/dev/null; HELD=0
  fi
  T0=$(date +%s)
  while [ $(( $(date +%s) - T0 )) -lt 10800 ]; do
    if gate; then
      if mkdir "$LOCK" 2>/dev/null; then
        if gate; then HELD=1; return 0; fi
        rmdir "$LOCK"
      fi
      sleep 0.01
    else
      sleep 3
    fi
  done
  return 1
}
BD=/DEV_TREE/lean
imports_ok() {   # every generated import (AggFive.*, L5S5.*) must have an olean newer than its source, else lake would rebuild it IN PARALLEL (an earlier out-of-memory incident)
  for I in $(grep -E '^import LRSpectrumFull\.(AggFive|L5S5)\.' "$BD/LRSpectrumFull/$(echo "$1" | tr . /).lean" | sed 's/^import LRSpectrumFull\.//'); do
    P=$(echo "$I" | tr . /)
    [ -f "$BD/.lake/build/lib/lean/LRSpectrumFull/$P.olean" ] && [ "$BD/.lake/build/lib/lean/LRSpectrumFull/$P.olean" -nt "$BD/LRSpectrumFull/$P.lean" ] || { echo "STALE IMPORT $I of $1"; return 1; }
  done
  return 0
}
rc=0
for M in "$@"; do
  NAME=$(echo "$M" | tr '.' '_')
  true
  TRY=0
  while :; do
    TRY=$((TRY+1))
    acquire || { echo "LOCK/GATE TIMEOUT before $M"; rc=9; break 2; }
    echo "build $M try $TRY $(date +%T)"
    rm -f "$LD/$NAME.out" "$LD/$NAME.watch"
    bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 12000 "$LD" "$NAME" bash -c "cd /DEV_TREE/lean && exec /usr/bin/time -l lake build LRSpectrumFull.$M"
    if grep -q "Build completed successfully" "$LD/$NAME.out" 2>/dev/null; then echo "done $M $(date +%T)"; break; fi
    rmdir "$LOCK" 2>/dev/null; HELD=0
    if grep -q "WATCHDOG KILL" "$LD/$NAME.watch" 2>/dev/null && [ $TRY -lt 6 ]; then echo "killed $M, waiting 10 min"; sleep 600; continue; fi
    echo "FAILED $M"; rc=1; break 2
  done
done
exit $rc
