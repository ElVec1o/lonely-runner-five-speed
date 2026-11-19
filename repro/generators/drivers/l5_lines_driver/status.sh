#!/bin/bash
# status.sh : one-screen status of the lines build (reads files only; safe from cron).
. /DEV_TREE/work/l5_lines_driver/common.sh
echo "=== LEAN5 LINES BUILD STATUS $(now) ==="
if [ -f $RO/driver.pid ] && kill -0 $(cat $RO/driver.pid) 2>/dev/null; then echo "driver: RUNNING pid $(cat $RO/driver.pid)"; else echo "driver: NOT RUNNING"; fi
[ -f $RO/STOP ] && echo "STOP file: $(cat $RO/STOP)"
echo "free disk: $(free_gb) GB (floor $DISK_FLOOR_GB)   lane lock: $([ -d $SLOT ] && echo held || echo free)   source MB (chunks+asm): $(du -sm $SRCC $RO/src_asm 2>/dev/null | awk '{s+=$1} END{print s+0}')"
echo "--- counts by status (results.tsv)"
awk -F'\t' 'NR>1{c[$6]++} END{for(s in c) printf "  %-9s %d\n", s, c[s]}' $RO/results.tsv 2>/dev/null
echo "  modules in order.txt: $(wc -l < $RO/order.txt) (chunks $(awk -F'\t' '$3=="chunk"' $RO/order.txt | wc -l)); chunks DONE: $(awk -F'\t' '$3=="chunk" && $6=="DONE"' $RO/results.tsv | wc -l)"
echo "--- running now"
awk -F'\t' 'NR>1 && $6=="RUNNING"{print "  ",$2,"node",$4,"points",$5,"since",$12}' $RO/results.tsv
echo "--- price vs model (0.70 ms/point + 34 ms/class + 0.5 s floor), DONE chunks"
awk -F'\t' 'FNR==NR{ncl[$1]=$4; pt[$1]=$5; next} FNR>1 && $3=="chunk" && $6=="DONE"{m=pt[$2]*0.0007+ncl[$2]*0.034+0.5; n++; mp+=m; cu+=$7; pts+=pt[$2]; if($8>pk)pk=$8; wl+=$10; if($9>0)k+=$9}
  END{ if(n>0) printf "  %d chunks: points %d, user CPU %.1f s, model %.1f s, ratio %.2f, ms/point (CPU, floor 0.5 s removed) %.3f, max peak %d MB, wall %d s, guard kills %d\n", n, pts, cu, mp, cu/mp, (cu-0.5*n)*1000/pts, pk, wl, k; else print "  no finished chunk yet" }' $PLAN $RO/results.tsv
echo "--- ETA"
awk -F'\t' 'FNR==NR{ncl[$1]=$4; pt[$1]=$5; next} FNR==1{next} {m=pt[$1]*0.0007+ncl[$1]*0.034+0.5; tot+=m} END{printf "  model total %.2f h CPU over %d chunks\n", tot/3600, NR}' $PLAN $PLAN 2>/dev/null | tail -1
awk -F'\t' 'FNR==NR{ncl[$1]=$4; pt[$1]=$5; m=pt[$1]*0.0007+ncl[$1]*0.034+0.5; tot+=m; next} FNR>1 && $3=="chunk" && $6=="DONE"{dm+=pt[$2]*0.0007+ncl[$2]*0.034+0.5; dc+=$7; dw+=$10; n++}
  END{ if(n>0){ r=dc/dm; rw=dw/dm; printf "  remaining model %.2f h; at measured CPU ratio %.2f: %.2f h CPU; at measured wall/model ratio %.2f (includes lake start and lane waits): %.2f h wall\n", (tot-dm)/3600, r, (tot-dm)*r/3600, rw, (tot-dm)*rw/3600 } else print "  no finished chunk yet" }' $PLAN $RO/results.tsv
echo "--- failures / kills"
awk -F'\t' 'NR>1 && ($6=="FAILED"||$6=="BLOCKED"||$6=="STOPPED"){print "  ",$2,$6,$14}' $RO/results.tsv | head -10
echo "  guard kills total: $(awk -F'\t' '$4=="KILL"{n++} END{print n+0}' $RO/modules.tsv 2>/dev/null)"
echo "--- axioms: DONE modules with non-STD axioms: $(awk -F'\t' 'NR>1 && $6=="DONE" && $11 !~ /^STD/' $RO/results.tsv | wc -l)"
echo "--- last events"
tail -n 5 $RO/events.log 2>/dev/null
