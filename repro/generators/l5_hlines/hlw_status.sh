#!/bin/bash
# hlw_status.sh : status of the S4W Hl loop (read-only)
D=/DEV_TREE/work/l5_hlines
OL=/DEV_TREE/lean/.lake/build/lib/lean/LRSpectrumFull
P=$(cat $D/state/hlw_forever.pid 2>/dev/null); kill -0 "$P" 2>/dev/null && echo "loop alive pid $P" || echo "loop NOT running"
[ -f $D/STOPW ] && echo "STOPW present"
echo "last cycles:"; tail -3 $D/state/hlw_cycles.tsv
$D/target/release/l5hlines status 2>/dev/null | head -12
echo "Hl.Top olean: $(stat -f %Sm $OL/AggFive/Hl/Top.olean)  Final2 olean: $(stat -f %Sm $OL/L5S5/FiveSpeedFinal2.olean)"
echo "lean RSS now: $(ps -Ao rss,command | grep '[b]in/lean ' | awk '{s+=$1} END{printf "%.1f GB", s/1048576}')"
