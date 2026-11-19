#!/bin/bash
# status.sh : per depth-1 node reps expected / built / holes, pending generated modules, and what the final module still needs.
# Read-only (no build, no lock).  usage: bash status.sh            (add `regen` as first argument to rerun the generator first)
P=/DEV_TREE
A=$P/work/l5_agg
L=$P/lean
B=$L/.lake/build/lib/lean/LRSpectrumFull
ARGS="$L $P/work/l5_rollout/results.tsv $P/work/l5s4s_gen/out3/rl3/T2RL_STATUS.tsv"
[ "$1" = regen ] && "$A/target/release/l5_agg" gen $ARGS
"$A/target/release/l5_agg" status $ARGS
echo "--- what the final module (L5S5.FiveSpeedFinal) still needs (observed from the build tree at $(date +%H:%M)) ---"
n3=$(ls $B/L5S4 | grep -cE '^GD3O(A)?[0-9]+\.olean$')
nlin=$(ls $B/L5S4 | grep -cE '^LinRQSC[0-9]+\.olean$')
echo "H6/H7 rep t3 modules (GD3O<c>.olean): $n3 files (a rep counts as built only if results.tsv says DONE/DONE_PRIOR with STD axioms, or it is listed in state/extra_built.txt)"
echo "H9    lines chunks LinRQSC<j>: $nlin of 1053 built; LinRAll: $( [ -f $B/L5S4/LinRAll.olean ] && echo built || echo MISSING ); LinRFinal: $( [ -f $B/L5S4/LinRFinal.olean ] && echo built || echo MISSING )"
echo "H8    registration LocRegistered C (topTab): $( [ -f $B/AggFive/Reg.olean ] && echo module present || echo NOT BUILT: hypothesis FiveSpeedHyps.reg )"
echo "H3    T5Store (ht5/hres): $( [ -f $B/L5S4/T5Store.olean ] && echo built || echo NOT BUILT: hypotheses ht5 and hres )"
echo "H7    reps 304 and 265: GD3O304.olean $( [ -f $B/L5S4/GD3O304.olean ] && echo present || echo absent ); GD3O265.olean $( [ -f $B/L5S4/GD3O265.olean ] && echo present || echo absent ); both stay holes until their axioms are observed and the rep is listed in state/extra_built.txt"
echo "Top/Final: Top.olean $( [ -f $B/AggFive/Top.olean ] && echo yes || echo no ), FiveSpeedFinal.olean $( [ -f $B/L5S5/FiveSpeedFinal.olean ] && echo yes || echo no ), AggBlock.olean $( [ -f $B/L5S5/AggBlock.olean ] && echo yes || echo no )"
echo "--- locks / machine ---"
ls -d $P/logs/LEAN_SLOT*.lock 2>/dev/null | sed 's|.*/||' | tr '\n' ' '; echo
ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "total lean RSS now: %.1f GB\n", s/1048576}'
df -h / | tail -1 | awk '{print "disk free:", $4}'
