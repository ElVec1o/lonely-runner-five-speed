#!/bin/bash
# buildstats.sh : per module family, number of modules built by lane.sh, sum of lake "Built ... (T s)" seconds, user CPU, maximum peak RSS (watch samples).
LD=/DEV_TREE/logs/l5agg
for f in $LD/AggFive_*.out $LD/L5S5_*.out; do
  n=$(basename $f .out)
  fam=$(echo "$n" | sed -E 's/[0-9]+/N/g')
  bs=$(grep -oE "Built LRSpectrumFull[A-Za-z0-9_.]* \([0-9.]+(ms|s)\)" "$f" | tail -1 | grep -oE "\([0-9.]+(ms|s)\)" | tr -d '()')
  usr=$(grep -E "^ +[0-9.]+ user" "${f%.out}.err" 2>/dev/null | awk '{print $1}' | head -1)
  [ -z "$usr" ] && usr=$(grep -E " user " "${f%.out}.err" 2>/dev/null | awk '{print $3}' | head -1)
  pk=$(grep -oE "rss=[0-9]+MB" "${f%.out}.watch" 2>/dev/null | tr -dc '0-9\n' | sort -n | tail -1)
  echo "$fam $n ${bs:-NA} ${usr:-NA} ${pk:-NA}"
done | awk '{fam=$1; n[fam]++; b=$3; if (b ~ /ms$/) {sub(/ms/,"",b); b=b/1000} else {sub(/s/,"",b)}; if ($3!="NA") bs[fam]+=b; if ($4!="NA") us[fam]+=$4; if ($5!="NA" && $5>pk[fam]) pk[fam]=$5} END{printf "%-34s %5s %10s %10s %9s\n","family","n","built_s","user_s","peakMB"; for (f in n) printf "%-34s %5d %10.1f %10.1f %9d\n", f, n[f], bs[f], us[f], pk[f]}' | sort
