#!/bin/bash
# loop.sh [INTERVAL_S]  (default 1800) : resumable detached loop that keeps the generated five-speed aggregation current.
#   one process (state/loop.pid); each cycle:
#     1. gen        : `l5_agg gen` regenerates the leaf masters / mids / roots / Top / FiveSpeedFinal for every rep that is now built
#                     (results.tsv DONE / DONE_PRIOR with STD axioms, or state/extra_built.txt); a file is rewritten only if its text changed.
#     2. build      : `l5_agg pending` (dependency order) -> ONE module at a time through lane2.sh (LANE 1 lock taken per module, 10 ms poll,
#                     disk >= 5 GB and guard gate waited for OUTSIDE the lock, 12 GB one-off wrapper, retry after a watchdog kill: 10 min, 6 times).
#     3. links      : `refresh_links.sh` (T2RL row-link modules) when at least LINKS_MIN (40) new GD3O oleans appeared since the last refresh.
#     4. snapshot   : status.sh output to logs/l5agg/loop_status_last.txt, one line to state/loop_cycles.tsv.
#   Never runs `gen` while build_all.sh runs (state/build_all.pid) and never runs two instances.
#   Stop: touch state/LOOP_STOP (finishes the current module, then exits).  Written by the loop itself on: a module above 8 GB peak (kill line),
#   a sorryAx/error in a generated module, the same module failing in 3 cycles, LOOP_MAXH (default 40 h) elapsed, disk below 3 GB.
#   Resume = run it again.   Own state only: state/loop.* and logs/l5agg/loop.log; never touches other seats' drivers, locks it did not create, or foreign processes.
P=/DEV_TREE
A=$P/work/l5_agg
L=$P/lean
LD=$P/logs/l5agg
S=$A/state
LOG=$LD/loop.log
ARGS="$L $P/work/l5_rollout/results.tsv $P/work/l5s4s_gen/out3/rl3/T2RL_STATUS.tsv"
B=$L/.lake/build/lib/lean/LRSpectrumFull
INTERVAL=${1:-1800}
MAXH=${LOOP_MAXH:-40}
LINKS_MIN=${LINKS_MIN:-40}
KILL_KB=$((8*1048576))
mkdir -p "$LD"
log() { echo "$(date '+%F %T') $*" >> "$LOG"; }
if [ -f "$S/loop.pid" ] && kill -0 "$(cat "$S/loop.pid")" 2>/dev/null; then echo "loop already running pid $(cat "$S/loop.pid")"; exit 1; fi
echo $$ > "$S/loop.pid"
trap 'rm -f "$S/loop.pid"; log "loop exit"' EXIT
rm -f "$S/LOOP_STOP"
T00=$(date +%s)
log "loop start pid $$ interval ${INTERVAL}s maxh ${MAXH} links_min ${LINKS_MIN}"
[ -f "$S/loop_modules.tsv" ] || printf 'time\tmodule\tstatus\twall_s\tpeak_MB\n' > "$S/loop_modules.tsv"
[ -f "$S/loop_cycles.tsv" ] || printf 'time\tcycle\tbuilt_reps\tholes\tpending_before\tmodules_built\tfailed\tfinal_olean\tnote\n' > "$S/loop_cycles.tsv"
LASTLINKS=$(ls $B/L5S4 | grep -cE '^GD3O(A)?[0-9]+\.olean$')   # links are refreshed from this base on; the first cycle does not refresh (done by hand before the loop)
stop() { echo "$1" > "$S/LOOP_STOP"; log "STOP written: $1"; }
strip_out() {   # $1 = dotted module: keep only the module's own lines + build verdict (the lake log replays every import's axiom lines)
  local M=$1 N=$(echo "$1" | tr . _) P2=$(echo "$1" | tr . /)
  local F=$LD/$N.out
  [ -f "$F" ] || return
  if grep -q "Build completed successfully" "$F"; then
    grep -E "LRSpectrumFull/$P2\.lean|Build completed successfully|declaration uses|sorryAx|error" "$F" > "$F.tmp"; mv "$F.tmp" "$F"
  else
    tail -n 200 "$F" > "$F.tmp"; mv "$F.tmp" "$F"
  fi
}
cycle=0
while :; do
  [ -f "$S/LOOP_STOP" ] && { log "LOOP_STOP seen: $(cat "$S/LOOP_STOP")"; break; }
  [ $(( $(date +%s) - T00 )) -gt $((MAXH*3600)) ] && { stop "max wall ${MAXH} h"; break; }
  DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}'); [ "$DG" -lt 3 ] && { stop "disk ${DG} GB"; break; }
  if [ -f "$S/build_all.pid" ] && kill -0 "$(cat "$S/build_all.pid")" 2>/dev/null; then log "build_all.sh is running (pid $(cat "$S/build_all.pid")): cycle skipped"; sleep 60; continue; fi
  cycle=$((cycle+1))
  TC=$(date +%s)
  GOUT=$("$A/target/release/l5_agg" gen $ARGS 2>&1 | tail -n 3 | tr '\n' ' ')
  log "cycle $cycle gen: $GOUT"
  BUILT=$(echo "$GOUT" | sed -n 's/.*built reps \([0-9]*\) of.*/\1/p'); HOLES=$(echo "$GOUT" | sed -n 's/.*holes \([0-9]*\).*/\1/p')
  PEND=$("$A/target/release/l5_agg" pending "$L" | tr '\n' ' ')
  NP=$(echo $PEND | wc -w | tr -d ' ')
  NB=0; NF=0; NOTE=""
  for M in $PEND; do
    [ -f "$S/LOOP_STOP" ] && { NOTE="stopped"; break; }
    N=$(echo "$M" | tr . _)
    T1=$(date +%s)
    OUT=$(bash "$A/lane2.sh" "$M" 2>&1); RC=$?
    W=$(( $(date +%s) - T1 ))
    PK=$(grep -o 'rss=[0-9]*MB' "$LD/$N.watch" 2>/dev/null | sed 's/rss=//; s/MB//' | sort -n | tail -n 1); PK=${PK:-0}
    if [ $RC -eq 0 ] && grep -q "Build completed successfully" "$LD/$N.out" 2>/dev/null; then
      if [ "$M" != "AggFive.Ctl" ] && grep -qE "sorryAx|declaration uses" "$LD/$N.out"; then
        strip_out "$M"; printf '%s\t%s\tSORRY\t%s\t%s\n' "$(date +%T)" "$M" "$W" "$PK" >> "$S/loop_modules.tsv"; stop "sorry/declaration-uses in generated module $M"; NF=$((NF+1)); break
      fi
      strip_out "$M"; NB=$((NB+1)); printf '%s\t%s\tOK\t%s\t%s\n' "$(date +%T)" "$M" "$W" "$PK" >> "$S/loop_modules.tsv"
      rm -f "$S/loopfail_$N"
      if [ $((PK*1024)) -gt $KILL_KB ]; then stop "module $M peak ${PK} MB above the 8 GB kill line"; break; fi
    else
      strip_out "$M"; NF=$((NF+1)); printf '%s\t%s\tFAIL rc=%s\t%s\t%s\n' "$(date +%T)" "$M" "$RC" "$W" "$PK" >> "$S/loop_modules.tsv"
      log "FAIL $M rc=$RC: $(echo "$OUT" | tail -n 2 | tr '\n' ' ')"
      K=$(cat "$S/loopfail_$N" 2>/dev/null || echo 0); K=$((K+1)); echo $K > "$S/loopfail_$N"
      [ $K -ge 3 ] && stop "module $M failed in 3 cycles (rc=$RC)"
      break    # dependents would fail: retry next cycle
    fi
  done
  # row links (T2RL) when enough new rep modules exist
  NOW=$(ls $B/L5S4 | grep -cE '^GD3O(A)?[0-9]+\.olean$')
  if [ ! -f "$S/LOOP_STOP" ] && [ $NF -eq 0 ] && [ $((NOW-LASTLINKS)) -ge $LINKS_MIN ]; then
    log "cycle $cycle: $((NOW-LASTLINKS)) new GD3O oleans, refresh_links LP$cycle"
    bash $P/logs/l5s4s/refresh_links.sh LP$cycle >> "$LOG" 2>&1 && LASTLINKS=$NOW || log "refresh_links LP$cycle returned nonzero"
    NOTE="$NOTE links"
  fi
  FIN=no; [ -f "$B/L5S5/FiveSpeedFinal.olean" ] && FIN=yes
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date +%T)" "$cycle" "${BUILT:-?}" "${HOLES:-?}" "$NP" "$NB" "$NF" "$FIN" "$NOTE" >> "$S/loop_cycles.tsv"
  log "cycle $cycle done in $(( $(date +%s) - TC )) s: pending $NP built $NB failed $NF final=$FIN"
  bash "$A/status.sh" > "$LD/loop_status_last.txt" 2>&1
  # wait INTERVAL (5 s polls of the stop file)
  W0=$(date +%s)
  while [ $(( $(date +%s) - W0 )) -lt "$INTERVAL" ]; do [ -f "$S/LOOP_STOP" ] && break; sleep 5; done
done
