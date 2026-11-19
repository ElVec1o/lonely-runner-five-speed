#!/bin/bash
# hlw_forever.sh [INTERVAL=1200] : S4W resumable loop for the Hl (lines mirror) family and FiveSpeedFinal2.
# Each cycle: (1) hl_build2.sh (regenerates l5hlines, builds only modules whose imports are fresh; lane 1 lock per batch, 9000 MB wrapper, disk >= 5 GB, lean RSS <= 8 GB gate);
#             (2) if AggFive.Hl.Top is fresher than L5S5.FiveSpeedFinal2 (or Final2 missing) and all its imports are fresh: build Final2 and record the axiom line;
#             (3) append a row to state/hlw_cycles.tsv: time, hole reps, built reps, m-fields, blocked, Top fresh, Final2 axioms.
# Never touches the agg loop or its locks.  Stop: touch l5_hlines/STOPW.  Self-stops: module peak > 8 GB in hl lane logs, any sorryAx in an Hl build log, 40 h, disk < 3 GB.
# Status: bash hlw_status.sh.  Restart after a stop: rm STOPW; nohup bash hlw_forever.sh >/dev/null 2>&1 </dev/null &
P=/DEV_TREE
D=$P/work/l5_hlines
LD=$P/logs/l5s4w
SRC=$P/lean
OL=$SRC/.lake/build/lib/lean/LRSpectrumFull
INT=${1:-1200}
echo $$ > $D/state/hlw_forever.pid
T0=$(date +%s)
[ -f $D/state/hlw_cycles.tsv ] || printf "time\thole_reps\tbuilt_reps\tm_fields\tblocked\tTop_fresh\tFinal2_axioms\n" > $D/state/hlw_cycles.tsv
fresh() { [ -f "$OL/$1.olean" ] && [ ! "$SRC/LRSpectrumFull/$1.lean" -nt "$OL/$1.olean" ]; }
while [ $(( $(date +%s) - T0 )) -lt 144000 ]; do
  [ -f $D/STOPW ] && { echo "$(date +%T) STOPW" >> $LD/hlw_forever.log; exit 0; }
  DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "$DG" -lt 3 ] && { echo "$(date +%T) disk $DG GB, stop" >> $LD/hlw_forever.log; exit 0; }
  : > $LD/hl/hl_blocked.log
  bash $D/hl_build2.sh >> $LD/hl/pipe.log 2>&1
  ST=$($D/target/release/l5hlines status 2>/dev/null | head -1)
  BL=$(grep -c . $LD/hl/hl_blocked.log)
  TF=no; fresh AggFive/Hl/Top && TF=yes
  AX=skip
  if [ $TF = yes ] && { [ ! -f $OL/L5S5/FiveSpeedFinal2.olean ] || [ $OL/AggFive/Hl/Top.olean -nt $OL/L5S5/FiveSpeedFinal2.olean ] || [ $OL/AggFive/Top.olean -nt $OL/L5S5/FiveSpeedFinal2.olean ]; }; then
    if fresh AggFive/Top && fresh L5S5/FinalGlue && fresh L5S4/CheckT1; then
      bash $D/lane_hl.sh L5S5.FiveSpeedFinal2 >> $LD/hl/final2.log 2>&1
      AX=$(grep 'five_speed_spectrum2' $LD/lane/L5S5_FiveSpeedFinal2.out | grep -o 'axioms: .*' | tail -1)
      [ -n "$AX" ] || AX=FAILED
    else AX=blocked_imports; fi
  fi
  # self-stop checks
  if grep -l 'sorryAx' $LD/lane/AggFive_Hl_*.out 2>/dev/null | head -1 | grep -q .; then echo "$(date +%T) sorryAx in an Hl log: stop" >> $LD/hlw_forever.log; touch $D/STOPW; fi
  PK=$(cat $LD/lane/AggFive_Hl_*.watch 2>/dev/null | grep -o 'rss=[0-9]*' | sed 's/rss=//' | sort -n | tail -1)
  [ "${PK:-0}" -gt 8000 ] && { echo "$(date +%T) peak $PK MB > 8000: stop" >> $LD/hlw_forever.log; touch $D/STOPW; }
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$(date +%T)" "$ST" "$BL" "$TF" "$AX" "" >> $D/state/hlw_cycles.tsv
  sleep $INT
done
