#!/bin/bash
# pipeline.sh : wait for reg_new.sh, build RegFin groups 7..9, regenerate the mirror, build it level by level.
P=/DEV_TREE
D=$P/work/l5_hlines
LD=$P/logs/l5hl
mkdir -p $LD
until grep -q "all done\|FAILED\|STOP" $P/logs/l5reg/reg_new.log; do sleep 10; done
grep -q "all done" $P/logs/l5reg/reg_new.log || { echo "$(date +%T) reg_new did not finish" >> $LD/pipeline.log; exit 1; }
bash $P/work/l5_reg/lane_reg.sh L5Reg.RegFin7 L5Reg.RegFin8 L5Reg.RegFin9 >> $LD/pipeline.log 2>&1 || { echo "$(date +%T) RegFin failed" >> $LD/pipeline.log; exit 1; }
$D/target/release/l5hlines gen >> $LD/pipeline.log 2>&1
bash $D/hl_build.sh >> $LD/pipeline.log 2>&1
echo "$(date +%T) pipeline end" >> $LD/pipeline.log
