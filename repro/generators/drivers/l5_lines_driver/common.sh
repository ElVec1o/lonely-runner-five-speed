#!/bin/bash
# common.sh : shared paths and helpers of the five-speed LINES build driver (lane 1, shares LEAN_SLOT.lock with l5_rollout).
P=/DEV_TREE
I=$P/work
RO=$I/l5_lines_driver
LEAN=$P/lean
L5=$LEAN/LRSpectrumFull/L5S4
OLEAN=$LEAN/.lake/build/lib/lean/LRSpectrumFull/L5S4
GL=/DEV_TREE/guard.log
SLOT=$P/logs/LEAN_SLOT4.lock
WRAP=$P/logs/rqlean/launch_oneoff_6000.sh
LAUNCH_SMALL=$I/l5probe4/launch_nogate.sh
EMIT=$RO/emit/target/release/l5qemit
TDIR=$I/lean5_data/src_t4_all
TSV=$(cat $RO/tsv_path.txt)
LINTL=$L5/LinTL.lean
PLAN=$RO/plan.tsv
SRCC=$RO/src_chunks          # emitted chunk sources, per batch of BATCH plan lines
BATCH=50
DISK_FLOOR_GB=3
SRC_BUDGET_MB=1024           # budget for NEW source text (src_chunks + src_asm + copies in the lean tree)
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
