#!/bin/bash
# fin.sh : generate RegFin0..RegFin6 (about 100 reps each, 265/304 excluded) and build them through lane_reg.sh
P=/DEV_TREE
L=$P/logs/l5reg
D=$P/work/l5_reg
grep -v -x -e 265 -e 304 $L/reps_all.txt > $L/reps_fin.txt
split -l 100 $L/reps_fin.txt $L/fin_grp_
g=0
MODS=""
for f in $L/fin_grp_*; do
  FORCE=1 bash $P/work/l5probe4/launch_nogate.sh 790 $L GENFIN$g $D/target/release/l5reg fin $g $(cat $f)
  MODS="$MODS L5Reg.RegFin$g"
  g=$((g+1))
done
echo "generated $g groups" >> $L/fin.log
bash $D/lane_reg.sh $MODS >> $L/fin.log 2>&1
echo "fin rc=$?" >> $L/fin.log
