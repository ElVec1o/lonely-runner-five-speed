#!/bin/bash
# measure.sh LABEL MODULE [MODULE...]   (dotted names under LRSpectrumFull; all must be BUILT)
# Cost of importing the aggregation: a tiny file `import <modules>` run by `lake env lean` (no olean written) under the lane-1 lock, then
# `lake build --no-build` of the same imports for the lake graph.  Appends a row to state/measure.tsv:
#   label  n_import_modules  closure_modules  closure_olean_MB  lean_maxRSS_MB  lean_wall_s  lake_graph_jobs  lake_maxRSS_MB  lake_wall_s
A=/DEV_TREE/work/l5_agg
L=/DEV_TREE/lean
LD=/DEV_TREE/logs/l5agg/meas
LOCK=/DEV_TREE/logs/LEAN_SLOT.lock
GL=/DEV_TREE/guard.log
LABEL=$1; shift; MODS="$*"
mkdir -p "$LD"
F=$LD/Meas_$LABEL.lean
{ for M in "$@"; do echo "import LRSpectrumFull.$M"; done; echo "#eval 0"; } > "$F"
CL=$("$A/target/release/l5_agg" closure "$L" $(for M in "$@"; do echo -n "LRSpectrumFull.$M "; done) | wc -l | tr -d ' ')
MB=$("$A/target/release/l5_agg" closure "$L" $(for M in "$@"; do echo -n "LRSpectrumFull.$M "; done) | sed 's/\./\//g' | while read p; do stat -f %z "$L/.lake/build/lib/lean/$p.olean" 2>/dev/null; done | awk '{s+=$1} END{printf "%.0f", s/1048576}')
LIM=$(grep 'guard started, limit' "$GL" | tail -1 | sed 's/.*limit \([0-9.]*\) GB.*/\1/'); LIM=${LIM:-20}
NEED=$(awk -v l="$LIM" 'BEGIN{printf "%d", (l-1.5-4.0)*1048576}')
T0=$(date +%s); GOT=0
while [ $(( $(date +%s) - T0 )) -lt 10800 ]; do mkdir "$LOCK" 2>/dev/null && { GOT=1; break; }; sleep 0.01; done
[ "$GOT" = 1 ] || { echo "LOCK TIMEOUT"; exit 9; }
trap 'rmdir "$LOCK" 2>/dev/null' EXIT
DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
FRK=$(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%d", s}')
if [ "${FRK:-0}" -gt "$NEED" ]; then echo "GATE FAIL mem (read-only run, no disk gate) lean_rss_kb=$FRK"; exit 5; fi
bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 12000 "$LD" "lean_$LABEL" bash -c "cd $L && exec /usr/bin/time -l lake env lean $F"
bash /DEV_TREE/logs/rqlean/launch_oneoff_6000.sh 12000 "$LD" "lake_$LABEL" bash -c "cd $L && exec /usr/bin/time -l lake build --no-build $(for X in $MODS; do echo -n LRSpectrumFull.$X' '; done)"
RSS1=$(grep 'maximum resident set size' "$LD/lean_$LABEL.err" | awk '{printf "%.0f", $1/1048576}')
W1=$(grep ' real ' "$LD/lean_$LABEL.err" | awk '{print $1}')
RSS2=$(grep 'maximum resident set size' "$LD/lake_$LABEL.err" | awk '{printf "%.0f", $1/1048576}')
W2=$(grep ' real ' "$LD/lake_$LABEL.err" | awk '{print $1}')
JOBS=$(grep -oE '\(([0-9]+) jobs\)' "$LD/lake_$LABEL.out" | tr -dc '0-9')
P=$(grep -c . "$F")
printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$LABEL" "$((P-1))" "$CL" "$MB" "$RSS1" "$W1" "${JOBS:-NA}" "$RSS2" "$W2" >> "$A/state/measure.tsv"
tail -1 "$A/state/measure.tsv"
