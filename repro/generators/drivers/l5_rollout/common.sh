#!/bin/bash
# common.sh : shared paths and helpers of the five-speed rollout driver (lane 1 only).
P=/DEV_TREE
RO=$P/work/l5_rollout
LEAN=$P/lean
L5=$LEAN/LRSpectrumFull/L5S4
OLEAN=$LEAN/.lake/build/lib/lean/LRSpectrumFull/L5S4
DATA=$P/work/lean5_data/src_v3r
GL=/DEV_TREE/guard.log
SLOT=${SLOT_OVERRIDE:-$P/logs/LEAN_SLOT3.lock}   # lane override (scratch runs on lane 1); unset = rollout lane 3
WRAP=$P/logs/rqlean/launch_oneoff_6000.sh
LAUNCH_SMALL=$P/work/l5probe4/launch_nogate.sh
L5S4O=$P/work/l5s4o_named/target/release/l5s4o   # same generator + main-module name table modname.tsv
DISK_FLOOR_GB=3
now() { date +%Y-%m-%dT%H:%M:%S; }
free_gb() { df -g /System/Volumes/Data | awk 'NR==2{print $4}'; }
elog() { echo "$(now) $*" >> $RO/events.log; }
# disk_gate: returns 0 when free disk >= floor; waits up to 30 min below the floor, then writes STOP and returns 1
disk_gate() {
  local t=0 f
  while true; do
    f=$(free_gb)
    [ "$f" -ge $DISK_FLOOR_GB ] && return 0
    [ -f $RO/STOP ] && return 1
    if [ $t -ge 1800 ]; then echo "disk free ${f} GB below ${DISK_FLOOR_GB} GB for 30 min" > $RO/STOP; elog "STOP written: disk ${f} GB"; return 1; fi
    sleep 60; t=$((t+60))
  done
}
# main-module name of a rep (table modname.tsv, rep TAB name; default GD3O<rep>).  Reps 1 and 2 collide with S4O library modules GD3O1, GD3O2.
main_of() { local m; m=$(awk -F'\t' -v r="$1" '$1==r{print $2; exit}' $RO/modname.tsv 2>/dev/null); echo "${m:-GD3O$1}"; }
