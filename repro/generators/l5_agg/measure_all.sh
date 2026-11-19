#!/bin/bash
A=/DEV_TREE/work/l5_agg
bash $A/measure.sh base L5S5.AggBlock
bash $A/measure.sh x100 $(cat $A/state/leaves100.txt)
bash $A/measure.sh x300 $(cat $A/state/leaves300.txt)
bash $A/measure.sh xALL $(cat $A/state/leavesALL.txt)
