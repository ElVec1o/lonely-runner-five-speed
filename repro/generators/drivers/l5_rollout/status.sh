#!/bin/bash
# status.sh : one-screen status of the rollout (safe to run from cron; reads files only).
. /DEV_TREE/work/l5_rollout/common.sh
echo "=== LEAN5 ROLLOUT STATUS $(now) ==="
if [ -f $RO/driver.pid ] && kill -0 $(cat $RO/driver.pid) 2>/dev/null; then echo "driver: RUNNING pid $(cat $RO/driver.pid)"; else echo "driver: NOT RUNNING"; fi
[ -f $RO/STOP ] && echo "STOP file: $(cat $RO/STOP)"
echo "free disk: $(free_gb) GB (floor $DISK_FLOOR_GB)   lane lock: $([ -d $SLOT ] && echo held || echo free)"
echo "--- counts by status (results.tsv)"
awk -F'\t' 'NR>1{c[$2]++} END{for(s in c) printf "  %-10s %d\n", s, c[s]}' $RO/results.tsv
TOT=$(wc -l < $RO/order.txt)
DONE=$(awk -F'\t' 'NR>1 && $2=="DONE"' $RO/results.tsv | wc -l)
echo "  normal reps in order.txt: $TOT, DONE here: $DONE, PRIOR (S4O): $(awk -F'\t' 'NR>1 && $2=="DONE_PRIOR"' $RO/results.tsv | wc -l), BLOCKED: $(awk -F'\t' 'NR>1 && $2=="BLOCKED"' $RO/results.tsv | wc -l)"
echo "--- running now"
awk -F'\t' 'NR>1 && $2=="RUNNING"{print "  rep",$1,"leaves",$3,"chunks",$4,"since",$12}' $RO/results.tsv
tail -n 3 $RO/modules.tsv 2>/dev/null | awk -F'\t' '{print "  last module:",$3,$4,"wall",$5,"s cpu",$6,"s peakMB",$7}'
echo "--- ETA (cost model: order.txt cost, calibrated by measured wall of finished reps)"
awk -F'\t' 'FNR==NR{cost[$1]=$2; next} FNR>1 && $2=="DONE"{ec+=cost[$1]; aw+=$10; n++} END{ if(n>0) printf "  finished %d reps: estimated %d s, measured wall %d s, ratio %.2f\n", n, ec, aw, aw/ec; else print "  no finished reps yet" }' $RO/order.txt $RO/results.tsv
awk -F'\t' 'FNR==NR{cost[$1]=$2; next} FNR>1 && $2=="DONE"{ec+=cost[$1]; aw+=$10; done[$1]=1} END{ }' $RO/order.txt $RO/results.tsv
R=$(awk -F'\t' 'FNR==NR{cost[$1]=$2; tot+=$2; next} FNR>1 && $2=="DONE"{ec+=cost[$1]; aw+=$10; d+=cost[$1]} END{ if(ec>0) printf "%.2f %d %d", aw/ec, tot-d, tot; }' $RO/order.txt $RO/results.tsv)
if [ -n "$R" ]; then set -- $R; awk -v r=$1 -v rem=$2 -v tot=$3 'BEGIN{printf "  remaining estimated cost %d s -> ETA %.1f h at ratio %.2f (cost model total %.1f h)\n", rem, rem*r/3600, r, tot/3600}'; fi
echo "--- failures / kills"
awk -F'\t' 'NR>1 && ($2=="FAILED"||$2=="STOPPED"){print "  rep",$1,$2,$14}' $RO/results.tsv | head -10
echo "  guard kills total: $(awk -F'\t' '$4=="KILL"{n++} END{print n+0}' $RO/modules.tsv 2>/dev/null)"
echo "--- last events"
tail -n 5 $RO/events.log 2>/dev/null
echo "--- axioms: reps DONE with non-STD axioms: $(awk -F'\t' 'NR>1 && ($2=="DONE"||$2=="DONE_PRIOR") && $11 !~ /^STD/' $RO/results.tsv | wc -l)"
