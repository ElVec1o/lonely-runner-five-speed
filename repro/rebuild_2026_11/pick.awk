# pick.awk: choose the first ready, unclaimed, not-dead modules in MANIFEST order.
# Files (by -v names): F_man F_dag F_res F_extra F_solo F_claims F_missing. Output lines: module pred_MB class bytes ceil_MB ; last line "#SUMMARY ..."
function fam(m,   g) { g = m; sub(/^LRSpectrumFull\./, "", g); gsub(/[0-9]+/, "#", g); return g }
function aggclass(m,   t) { t = m; sub(/^LRSpectrumFull\./, "", t);
  return (t ~ /^L5S5(\.|$)/ || t ~ /^AggFive(\.|$)/ || t ~ /FiveSpeedFinal|Master|Final|Top|Root|Mid|Leaf/) }
FILENAME==F_man { if (FNR>1) { n++; mod[n]=$2; sha[$2]=$4; byt[$2]=$5+0 } next }
FILENAME==F_dag { imp[$1]=$2; next }
FILENAME==F_res { if (FNR>1) { st[$1]=$3; tr[$1]=$4
    if ($3=="OK" && $2==sha[$1]) { ok[$1]=1
      if ($6 ~ /^[0-9]+$/) { g=fam($1); pk=$6+0; if (pk>fmax[g]) fmax[g]=pk; fcnt[g]++; if (byt[$1]>fb[g]) fb[g]=byt[$1] } } } next }
FILENAME==F_extra { ok[$1]=1; next }
FILENAME==F_solo { solo[$1]=1; next }
FILENAME==F_claims { claimed[$1]=1; next }
FILENAME==F_missing { miss[$1]=1; next }
END {
  for (m in miss) delete ok[m]
  cnt=0; nb=0; nd=0; nrem=0
  for (i=1;i<=n;i++) { m=mod[i]
    if (ok[m]) continue
    if (st[m]=="FAIL" && (tr[m]=="try2" || tr[m]=="try0")) { nd++; continue }
    nrem++
    if (m in claimed) continue
    ready=1; k=split(imp[m], a, ",")
    for (j=1;j<=k;j++) if (a[j]!="" && !ok[a[j]]) { ready=0; break }
    if (!ready) { nb++; continue }
    g=fam(m); measured = (fcnt[g]>=3 && byt[m] <= 1.5*fb[g])
    pred = measured ? int(fmax[g]*1.15+0.999) : 9000
    cls="NORMAL"; ceil=9000
    if (st[m]=="FAIL" && tr[m]=="try1") { cls="ALONE_RETRY12"; ceil=12000; pred=12000 }
    else if (m in solo) { cls="ALONE_SOLO"; if (pred<9000) pred=9000 }
    else if (aggclass(m)) { cls="ALONE_AGG"; if (pred<9000) pred=9000 }
    else if (!measured) { cls="ALONE_UNMEAS" }
    printf "%s\t%d\t%s\t%d\t%d\t%s\n", m, pred, cls, byt[m], ceil, g
    if (++cnt>=5) break
  }
  printf "#SUMMARY remaining_nonfailed=%d blocked_by_deps=%d dead=%d\n", nrem, nb, nd
}
