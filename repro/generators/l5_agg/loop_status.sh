#!/bin/bash
# loop_status.sh : read-only status of the aggregation loop (loop.sh).  usage: bash loop_status.sh        (add `full` to append status.sh)
P=/DEV_TREE
A=$P/work/l5_agg
S=$A/state
LD=$P/logs/l5agg
B=$P/lean/.lake/build/lib/lean/LRSpectrumFull
if [ -f $S/loop.pid ] && kill -0 "$(cat $S/loop.pid)" 2>/dev/null; then echo "loop: RUNNING pid $(cat $S/loop.pid), started $(ps -o lstart= -p $(cat $S/loop.pid))"; else echo "loop: NOT running"; fi
[ -f $S/LOOP_STOP ] && echo "STOP file: $(cat $S/LOOP_STOP)"
echo "--- last log lines"; tail -n 6 $LD/loop.log 2>/dev/null
echo "--- last cycles (time cycle built_reps holes pending_before built failed final_olean note)"; tail -n 5 $S/loop_cycles.tsv 2>/dev/null
echo "--- modules: OK $(awk -F'\t' '$3=="OK"' $S/loop_modules.tsv | wc -l), FAIL $(awk -F'\t' '$3 ~ /^FAIL|^SORRY/' $S/loop_modules.tsv | wc -l); max peak $(awk -F'\t' 'NR>1 && $5+0>m{m=$5+0} END{print m+0}' $S/loop_modules.tsv) MB; last 5:"
tail -n 5 $S/loop_modules.tsv
echo "--- the big three (observed oleans / logs)"
for m in AggFive/Top L5S5/FiveSpeedFinal; do printf '%s: ' $m; [ -f $B/$m.olean ] && echo "olean present" || echo "not built"; done
grep -E "^[0-9:]+\s+(AggFive.Top|L5S5.FiveSpeedFinal)\s" $S/loop_modules.tsv | tail -n 4
echo "--- pending now: $("$A/target/release/l5_agg" pending $P/lean | wc -l | tr -d ' ') generated modules"
[ "$1" = full ] && bash $A/status.sh
echo "stop:   touch $S/LOOP_STOP      restart: nohup bash $A/loop.sh 1800 >/dev/null 2>&1 </dev/null &"
