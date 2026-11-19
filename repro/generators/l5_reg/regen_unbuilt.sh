#!/bin/bash
# regen_unbuilt.sh : rewrite Reg<c>.lean (current generator text, maxHeartbeats 0) for every rep without an olean (except 265, 304), then restart bulk.sh
P=/DEV_TREE
L=$P/logs/l5reg
OL=$P/lean/.lake/build/lib/lean/LRSpectrumFull/L5Reg
D=$P/work/l5_reg
R=""
for c in $(cat $L/reps_all.txt); do
  if [ "$c" = 304 ] || [ "$c" = 265 ]; then continue; fi
  if [ ! -f $OL/Reg$c.olean ]; then R="$R $c"; fi
done
echo "regen for $(echo $R | wc -w) reps"
FORCE=1 bash $P/work/l5probe4/launch_nogate.sh 790 $L GENB3 $D/target/release/l5reg gen $R
tail -1 $L/GENB3.err
rm -f $L/bulk_batch_*
nohup bash $D/bulk.sh > /dev/null 2>&1 < /dev/null &
disown
