#!/bin/bash
# probe.sh LABEL FILE [lean args...]   (S4W, 2026-11-18)
# One memory probe: `lake env lean FILE` under /usr/bin/time -l, through launch_oneoff_6000.sh with a 9000 MB ceiling (watchdog kills at 8100 MB).
# Gates (outside the lock, poll 3 s, up to 3 h): free disk >= 5 GB and TOTAL lean RSS (ps, all lean processes) <= 8 GB.
# Lock: lane 1 (LEAN_SLOT.lock), 10 ms poll, released only if this script created it.  Appends a row to l5_hlines/state/probe.tsv:
#   label  peak_RSS_MB  peak_footprint_MB  wall_s  exit  killed
LOCK=/DEV_TREE/logs/LEAN_SLOT.lock
LD=/DEV_TREE/logs/l5s4w/probes
HD=/DEV_TREE/work/l5_hlines
L=/DEV_TREE/lean
LABEL=$1; F=$2; shift 2; XARGS="$*"
mkdir -p "$LD"
gate() {
  DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
  FRK=$(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%d", s}')
  [ "$DG" -ge 3 ] && [ "${FRK:-0}" -le 8388608 ]
}
HELD=0
trap '[ "$HELD" = 1 ] && rmdir "$LOCK" 2>/dev/null' EXIT
T0=$(date +%s)
while [ $(( $(date +%s) - T0 )) -lt 10800 ]; do
  if gate; then
    if mkdir "$LOCK" 2>/dev/null; then
      if gate; then HELD=1; break; fi
      rmdir "$LOCK"
    fi
    sleep 0.01
  else
    sleep 3
  fi
done
[ "$HELD" = 1 ] || { echo "GATE/LOCK TIMEOUT $LABEL"; exit 9; }
rm -f "$LD/$LABEL.out" "$LD/$LABEL.err" "$LD/$LABEL.watch"
echo "start $LABEL $(date +%T)"
bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 9000 "$LD" "$LABEL" bash -c "cd $L && exec /usr/bin/time -l lake env lean $XARGS $F"
rmdir "$LOCK" 2>/dev/null; HELD=0
RSS=$(grep 'maximum resident set size' "$LD/$LABEL.err" | awk '{printf "%.0f", $1/1048576}')
FP=$(grep 'peak memory footprint' "$LD/$LABEL.err" | awk '{printf "%.0f", $1/1048576}')
W=$(grep ' real ' "$LD/$LABEL.err" | awk '{print $1}')
EX=$(grep '^exit=' "$LD/$LABEL.watch" | tail -1 | sed 's/exit=\([0-9]*\).*/\1/')
KL=$(grep -c 'WATCHDOG KILL' "$LD/$LABEL.watch")
PK=$(grep -o 'rss=[0-9]*' "$LD/$LABEL.watch" | sed 's/rss=//' | sort -n | tail -1)
printf "%s\t%s\t%s\t%s\t%s\t%s\twatch_peak=%s\n" "$LABEL" "${RSS:-NA}" "${FP:-NA}" "${W:-NA}" "${EX:-NA}" "$KL" "${PK:-NA}" >> "$HD/state/probe.tsv"
tail -1 "$HD/state/probe.tsv"
