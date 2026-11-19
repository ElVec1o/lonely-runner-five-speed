#!/bin/bash
cd /DEV_TREE/work/lean5_wp0a
L=../../logs/rank_awindow_review/launch_nogate.sh
bash $L 780 out var_inclhi ./target/release/wp0a_v2 tree --inclhi
bash $L 780 out var_emul32 ./target/release/wp0a_v2 tree --emul32
echo done > out/variants.done
