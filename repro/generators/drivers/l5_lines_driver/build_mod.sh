#!/bin/bash
# build_mod.sh MOD TAG : build ONE module LRSpectrumFull.L5S4.MOD on lane 1 via the one-off wrapper (ceiling 12000, tree watchdog), with
#   - the lane lock (atomic mkdir of LEAN_SLOT.lock, shared with the l5_rollout driver and the other seats), released after every module,
#   - the global guard gate (total lean RSS + 6.5 GB <= guard limit - 1.5 GB), disk gate (>= 5 GB),
#   - an own 9 GB tree-RSS killer (kill line: no process tree above 9 GB),
#   - retry on guard/watchdog kills: wait 10 min, up to 6 retries.
# modules.tsv row: time TAG MOD STATUS wall user_s maxrss_MB watch_peak_MB guard_kills attempts
# exit: 0 ok, 10 real error, 11 kills exhausted, 13 lane wait timeout, 14 disk, 20 STOP, 3 import not built
. /DEV_TREE/work/l5_lines_driver/common.sh
M=$1; REP=$2
LD=$RO/logs/mod; mkdir -p $LD
for imp in $(grep -E '^import LRSpectrumFull\.L5S4\.' $L5/$M.lean | sed 's/^import LRSpectrumFull\.L5S4\.//'); do
  [ -f $OLEAN/$imp.olean ] || { echo "$(now)	$REP	$M	IMPORT_NOT_BUILT:$imp	0	0	0	0	0	0" >> $RO/modules.tsv; exit 3; }
done
HELD=0
trap '[ $HELD = 1 ] && rmdir $SLOT 2>/dev/null' EXIT
ATT=0; GK=0
while [ $ATT -lt 7 ]; do
  ATT=$((ATT+1))
  [ -f $RO/STOP ] && exit 20
  disk_gate || exit 14
  # ---- lane + guard gate
  WAITED=0
  while true; do
    [ -f $RO/STOP ] && exit 20
    LIM=$(grep 'guard started, limit' $GL | tail -1 | sed 's/.*limit \([0-9.]*\) GB.*/\1/'); LIM=${LIM:-16}
    RSSMB=$(ps -Ao rss,command | grep '[b]in/lean' | awk '{s+=$1} END{print int(s/1024)}')
    DG=$(free_gb)
    OKMEM=$(awk -v r=$RSSMB -v l=$LIM 'BEGIN{ if ((r/1024 + 4.0) <= (l - 1.5)) print 1; else print 0 }')
    if [ "$DG" -ge $DISK_FLOOR_GB ] && [ "$OKMEM" = "1" ]; then
      if mkdir $SLOT 2>/dev/null; then HELD=1; break; fi
    fi
    [ $WAITED -ge 72000 ] && { echo "$(now)	$REP	$M	LANE_TIMEOUT	0	0	0	0	$GK	$ATT" >> $RO/modules.tsv; exit 13; }
    sleep 0.2; WAITED=$((WAITED+1))   # fast poll: the other lane drivers re-lock within milliseconds; WAITED counts 5 polls per second (limit 14400 s = 72000)
  done
  GLN0=$(wc -l < $GL)
  rm -f $LD/$M.out $LD/$M.err $LD/$M.watch $LD/$M.k9
  S=$(date +%s)
  bash $WRAP 12000 $LD $M /usr/bin/time -l bash -c "cd $LEAN && lake build LRSpectrumFull.L5S4.$M" &
  WP=$!
  ( while kill -0 $WP 2>/dev/null; do
      TREE=$(ps -axo pid=,ppid=,rss= | awk -v r=$WP '{pp[$1]=$2; rs[$1]=$3} END{t[r]=1; do{c=0; for(p in pp) if(!(p in t) && (pp[p] in t)){t[p]=1;c=1}}while(c); s=0; l=""; for(p in t){s+=rs[p]; l=l" "p}; print s, l}')
      RSS=${TREE%% *}; PIDS=${TREE#* }
      if [ -n "$RSS" ] && [ "$RSS" -gt 9437184 ]; then echo "KILL9G rss=$((RSS/1024))MB" > $LD/$M.k9; kill $PIDS 2>/dev/null; break; fi
      sleep 3
    done ) &
  KP=$!
  wait $WP
  kill $KP 2>/dev/null; wait $KP 2>/dev/null
  rmdir $SLOT 2>/dev/null; HELD=0
  W=$(( $(date +%s) - S ))
  USR=$(grep -E ' real ' $LD/$M.err | tail -1 | awk '{print $3}')
  MXB=$(grep 'maximum resident set size' $LD/$M.err | tail -1 | awk '{print int($1/1048576)}')
  PEAKW=$(grep -o 'rss=[0-9]*MB' $LD/$M.watch 2>/dev/null | sed 's/rss=//;s/MB//' | sort -n | tail -1)
  ST=ERROR
  if grep -q "Build completed successfully" $LD/$M.out 2>/dev/null; then ST=OK
  elif [ -f $LD/$M.k9 ] || grep -q WATCHDOG $LD/$M.watch 2>/dev/null; then ST=KILL
  elif [ "$(wc -l < $GL)" -gt "$GLN0" ] && tail -n +$((GLN0+1)) $GL | grep -q 'killing'; then ST=KILL
  elif grep -qE 'exit code 137|code 137|Killed' $LD/$M.out $LD/$M.err 2>/dev/null; then ST=KILL
  fi
  echo "$(now)	$REP	$M	$ST	$W	${USR:-0}	${MXB:-0}	${PEAKW:-0}	$GK	$ATT" >> $RO/modules.tsv
  case $ST in
    OK) exit 0;;
    ERROR) exit 10;;
    KILL) GK=$((GK+1)); elog "kill on $M (attempt $ATT): waiting 10 min"
          [ $ATT -ge 7 ] && exit 11
          for i in $(seq 1 60); do [ -f $RO/STOP ] && exit 20; sleep 10; done;;
  esac
done
exit 11
