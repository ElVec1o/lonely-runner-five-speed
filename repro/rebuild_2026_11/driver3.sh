#!/bin/bash
# driver3.sh (2026-11-22, REBUILD-FAILURES seat; copy of driver2.sh with the 16 GB solo-retry policy; driver2.sh and driver.sh unchanged for rollback). Original header: driver2.sh: two-lane, dependency-aware, admission-controlled rebuild driver (bash 3.2; no associative arrays).
# Modes: (none)=run | --dryrun | --test-dag | --mkdag
# Same results.tsv format and same per-module launcher as driver.sh (which is kept unchanged for rollback).
# Safety design: strict manifest order among READY modules; a module is READY only when every import has an OK row (sha match) and an .olean;
# admission by predicted peak; unmeasured/aggregation/retry/monitor-killed modules run ALONE; monitor kills only the newest lane's module above 15.5 GB.
P=/PATH/TO/programme
RB=$P/private/rebuild_five
CK=$RB/checkout; LEAN=$CK/lean; MAN=$RB/manifest3.tsv; RES=$RB/results.tsv
LOGD=$RB/logs; LAUNCH=$P/private/logs/rqlean/launch_oneoff_6000.sh
CKPT=$P/NEXT_BIG/H_rebuild/CHECKPOINT.md
DAG=$RB/dag3.tsv; PICK=$RB/pick3.awk; LANES=$RB/lanes
CEIL=9000; CEIL_RETRY=16000; RETRY_FOREIGN_CAP_MB=19000   # retry runs ALONE; abort/defer if foreign lean RSS + 16000 > 19000
ADMIT_MB=13000      # ours: committed + predicted <= this to admit a 2nd module
ADMIT_ALL_MB=18000  # ours + foreign lean + predicted <= this (foreign guard kills at 20 GB total)
KILL_MB=15500       # monitor threshold on summed RSS of our lean processes
DISK_ADMIT_GB=15; DISK_STOP_GB=10; PAUSE_S=600
export PATH=$HOME/.elan/bin:$PATH
MODE=${1:-run}
ERRLOG=$RB/errors.log
mkdir -p "$LOGD" "$LANES/claims" "$LANES/solo" "$P/NEXT_BIG/H_rebuild"
[ -f "$RES" ] || printf 'module\tsha256\tstatus\ttry\twall_s\tpeak_MB\n' > "$RES"
START_FILE=$RB/driver.start; [ -f "$START_FILE" ] || date +%s > "$START_FILE"
T0=$(cat "$START_FILE")
NTOT=$(($(wc -l < "$MAN")-1)); TOTBYTES=$(awk -F'\t' 'NR>1{s+=$5} END{print s}' "$MAN")

free_gb() { df -g /System/Volumes/Data | awk 'NR==2{print $4}'; }
stopfile() { [ -e "$RB/STOP" ] || [ -e "$P/NEXT_BIG/PAUSE" ] || [ -e "$P/private/INVENTION_2026_11/NEXT_BIG/PAUSE" ]; }
live_ours() { ps -axo rss=,command= | awk '/bin\/lean / && /rebuild_five\/checkout/ {s+=$1} END{print int(s/1024)}'; }
live_foreign() { ps -axo rss=,command= | awk '/bin\/lean / && !/rebuild_five\/checkout/ {s+=$1} END{print int(s/1024)}'; }

# ---------- sched lock (short critical sections) ----------
sched_acquire() { local i=0
  while ! mkdir "$SD/sched.lock" 2>/dev/null; do
    sleep 1; i=$((i+1))
    if [ $i -ge 30 ]; then op=$(cat "$SD/sched.lock/pid" 2>/dev/null); if [ -n "$op" ] && ! kill -0 "$op" 2>/dev/null; then rm -rf "$SD/sched.lock"; fi; i=0; fi
  done; echo $$ > "$SD/sched.lock/pid"; }
sched_release() { rm -rf "$SD/sched.lock"; }

# cur file: module TAB pred TAB start TAB alone TAB launcherpid
write_cur() { printf '%s\t%s\t%s\t%s\t%s\n' "$2" "$3" "$4" "$5" "$6" > "$SD/$1.cur.tmp" && mv "$SD/$1.cur.tmp" "$SD/$1.cur"; }
others_cur() { ls "$SD" 2>/dev/null | grep '\.cur$' | grep -v "^$1\.cur$"; }

# decide LANE: sets D_RES (TAKE|ALONEWAIT|WAIT|DONE), D_MOD D_PRED D_CLS D_BYTES D_CEIL D_WHY. Needs SD, RESF, EXTRA, DRYLIVE (sim live rss or empty)
decide() {
  local L=$1 T=$SD/tmp.$L
  ls "$SD/claims" > "$T.claims" 2>/dev/null; ls "$SD/solo" > "$T.solo" 2>/dev/null; : > "$T.empty"
  [ -f "$SD/defer.tsv" ] && awk -F"\t" -v n=$(date +%s) '$2>n{print $1}' "$SD/defer.tsv" >> "$T.claims"   # driver3: modules whose 16 GB retry was deferred (foreign RSS)
  [ -f "$SD/missing.txt" ] || : > "$SD/missing.txt"; [ -n "$EXTRA" ] || EXTRA=$T.empty
  local OUT; OUT=$(awk -F'\t' -v F_man="$MAN" -v F_dag="$DAG" -v F_res="$RESF" -v F_extra="$EXTRA" -v F_solo="$T.solo" -v F_claims="$T.claims" -v F_missing="$SD/missing.txt" -f "$PICK" "$MAN" "$DAG" "$RESF" "$EXTRA" "$T.solo" "$T.claims" "$SD/missing.txt")
  local SUM; SUM=$(echo "$OUT" | grep '^#SUMMARY'); local C; C=$(echo "$OUT" | grep -v '^#' | head -1)
  local others; others=$(others_cur "$L"); local nother; nother=$(echo "$others" | grep -c .)
  D_RES=WAIT; D_MOD=; D_WHY=
  if [ -z "$C" ]; then
    if [ "$nother" = 0 ] && ! ls "$SD" | grep -q '^want_alone\.'; then D_RES=DONE; else D_WHY="no ready module (other lane running)"; fi
    D_WHY="${D_WHY:-no ready module and nothing running}; $SUM"; return
  fi
  D_MOD=$(echo "$C" | cut -f1); D_PRED=$(echo "$C" | cut -f2); D_CLS=$(echo "$C" | cut -f3); D_BYTES=$(echo "$C" | cut -f4); D_CEIL=$(echo "$C" | cut -f5)
  # dependency .olean check (belt and braces; a missing one is recorded and the pick is recomputed next cycle)
  local d ol; for d in $(awk -F'\t' -v m="$D_MOD" '$1==m{print $2}' "$DAG" | tr ',' ' '); do
    ol="$LEAN/.lake/build/lib/lean/$(echo "$d" | sed 's#^LRSpectrumFull\.##; s#\.#/#g; s#^#LRSpectrumFull/#').olean"
    if [ -z "$DRY" ] && [ ! -f "$ol" ]; then echo "$d" >> "$SD/missing.txt"; D_RES=WAIT; D_WHY="dep olean missing for $D_MOD: $d (recorded)"; return; fi
  done
  if ls "$SD" | grep -q '^want_alone\.' && ! [ -e "$SD/want_alone.$L" ]; then D_WHY="other lane waits for solo slot"; return; fi
  if [ "$D_CLS" != NORMAL ]; then
    if [ "$nother" = 0 ]; then D_RES=TAKE; D_WHY="$D_CLS: alone, nothing else running"; else D_RES=ALONEWAIT; D_WHY="$D_CLS: needs the machine alone (pred $D_PRED MB), $nother other running"; fi
    return
  fi
  # NORMAL class
  if [ "$nother" = 0 ]; then D_RES=TAKE; D_WHY="NORMAL, nothing else running (pred $D_PRED MB)"; return; fi
  local f alone=0 sumpred=0 line
  for f in $others; do line=$(cat "$SD/$f"); [ "$(echo "$line" | cut -f4)" = 1 ] && alone=1; sumpred=$((sumpred + $(echo "$line" | cut -f2))); done
  if [ $alone = 1 ]; then D_WHY="a running module holds the machine alone"; return; fi
  local pu; pu=$(cat "$SD/pause_until" 2>/dev/null); pu=${pu:-0}
  if [ "$(date +%s)" -lt "$pu" ]; then D_WHY="2nd-lane admissions paused for $((pu-$(date +%s))) s after a monitor kill"; return; fi
  local live fo; if [ -n "$DRYLIVE" ]; then live=$DRYLIVE; fo=0; else live=$(live_ours); fo=$(live_foreign); fi
  local committed=$live; [ $sumpred -gt $committed ] && committed=$sumpred
  local gb; gb=$(free_gb); [ -n "$DRYFREE" ] && gb=$DRYFREE
  if [ "$gb" -lt "$DISK_ADMIT_GB" ]; then D_WHY="free disk ${gb} GB < $DISK_ADMIT_GB"; return; fi
  if [ $((committed + D_PRED)) -gt $ADMIT_MB ]; then D_WHY="committed $committed (live $live, preds $sumpred) + pred $D_PRED > $ADMIT_MB"; return; fi
  if [ $((committed + fo + D_PRED)) -gt $ADMIT_ALL_MB ]; then D_WHY="ours $committed + foreign $fo + pred $D_PRED > $ADMIT_ALL_MB"; return; fi
  D_RES=TAKE; D_WHY="NORMAL, committed $committed + pred $D_PRED <= $ADMIT_MB (foreign $fo)"
}

# ---------- status ----------
LASTST=0
status() {
  local now=$(date +%s) el done fail blocked peak free sumw lastm lanesinfo rss samp
  el=$((now-T0)); NTOT=$(($(wc -l < "$MAN")-1))
  done=$(awk -F'\t' '$3=="OK"{d[$1]=1} END{n=0; for(k in d)n++; print n}' "$RES")
  fail=$(awk -F'\t' 'NR>1{s[$1]=$3} END{n=0; for(k in s) if(s[k]=="FAIL")n++; print n}' "$RES")
  peak=$(awk -F'\t' '$3=="OK"&&$6!="NA"&&$6+0>m{m=$6+0; mm=$1} END{print m+0, mm}' "$RES")
  sumw=$(awk -F'\t' '$3=="OK"{s+=$5} END{print s+0}' "$RES")
  free=$(free_gb); lastm=$(tail -1 "$RES" | cut -f1,3,5)
  lanesinfo=$(for f in "$LANES"/*.cur; do [ -f "$f" ] && echo "$(basename $f .cur): $(cut -f1,2,4 $f | tr '\t' ' ')"; done | tr '\n' ';')
  cat > "$RB/STATUS.md" <<EOF
# REBUILD five-speed v1.0.1 (HEAD $(git -C "$CK" rev-parse --short HEAD)) status $(date '+%F %T')  [driver3, 2 lanes, 16 GB solo retry]
- modules OK: $done / $NTOT ; failed (latest status FAIL): $fail
- elapsed since first launch (wall): $((el/3600)) h $((el%3600/60)) min ; summed module wall time: $sumw s (two lanes overlap, so wall < summed)
- lanes running: $(ls "$LANES" | grep -c '\.cur$') of 2 -> ${lanesinfo:-none}
- summed lean RSS of ours now: $(live_ours) MB (foreign lean: $(live_foreign) MB); max summed RSS sampled by monitor: $(cat "$LANES/peak_sum" 2>/dev/null || echo NA) MB (kill threshold $KILL_MB)
- monitor kills (retry-later): $(grep -c . "$LANES/retry.log" 2>/dev/null || echo 0)
- max peak RSS of a built module: $peak MB (ceiling $CEIL MB)
- free disk: ${free} GB (stop and checkpoint below $DISK_STOP_GB GB)
- last result row: $lastm
- driver3 pid: $$ ; stop files: $( [ -e "$RB/STOP" ] && echo "STOP present"; [ -e "$P/NEXT_BIG/PAUSE" ] && echo "PAUSE present" )
EOF
  cp "$RB/STATUS.md" "$CKPT"; LASTST=$now
}

# ---------- monitor ----------
monitor() {
  local n=0 pk=0
  while :; do
    local o; o=$(live_ours); n=$((n+1))
    if [ "$o" -gt "$pk" ]; then pk=$o; echo "$pk" > "$LANES/peak_sum.tmp" && mv "$LANES/peak_sum.tmp" "$LANES/peak_sum"; fi
    if [ $((n%5)) = 0 ]; then printf '%s\t%s\t%s\t%s\n' "$(date +%s)" "$o" "$(live_foreign)" "$(ls "$LANES" | grep -c '\.cur$')" >> "$LANES/samples.tsv"; fi
    if [ "$o" -gt "$KILL_MB" ] && [ "$(ls "$LANES" | grep -c '\.cur$')" -ge 2 ]; then
      # newest module = largest start time
      local victim=; local vs=0 f s
      for f in "$LANES"/*.cur; do s=$(cut -f3 "$f"); if [ "$s" -ge "$vs" ]; then vs=$s; victim=$f; fi; done
      local vl; vl=$(basename "$victim" .cur); [ -e "$LANES/killed.$vl" ] && { sleep 2; continue; }; local vm; vm=$(cut -f1 "$victim"); local lp; lp=$(cut -f5 "$victim")
      echo "$(date +%T) MONITOR: ours ${o} MB > $KILL_MB; killing newest lane $vl module $vm (launcher $lp); retry-later, 2nd-lane admissions paused ${PAUSE_S}s" | tee -a "$LANES/retry.log" >> "$ERRLOG"
      echo "$vm" > "$LANES/killed.$vl"; echo $(( $(date +%s) + PAUSE_S )) > "$LANES/pause_until"
      if [ -n "$lp" ] && [ "$lp" != 0 ]; then
        local tree; tree=$(ps -axo pid=,ppid= | awk -v r=$lp '{pp[$1]=$2} END{t[r]=1; do{c=0; for(p in pp) if(!(p in t) && (pp[p] in t)){t[p]=1;c=1}}while(c); l=""; for(p in t) l=l" "p; print l}')
        kill $tree 2>/dev/null; sleep 4; kill -9 $tree 2>/dev/null
      fi
    fi
    sleep 2
  done
}

# ---------- one module ----------
# run_module LANE MOD PRED CLS BYTES CEIL ; handles sha check, tries, results rows, retry, kill marker.
run_module() {
  local L=$1 m=$2 pred=$3 cls=$4 ceil=$5 nm path h src act try c W peak S LP ok=0 alone=0
  nm=$(echo "$m" | tr '.' '_')
  read -r path h < <(awk -F'\t' -v m="$m" '$2==m{print $3"\t"$4}' "$MAN" | tr '\t' ' ')
  [ "$cls" != NORMAL ] && alone=1
  src="$LEAN/$path"; act=$(shasum -a 256 "$src" 2>/dev/null | cut -d' ' -f1)
  if [ "$act" != "$h" ]; then printf '%s\t%s\tFAIL\ttry0\t0\tNA\n' "$m" "$h" >> "$RES"; echo "SHA MISMATCH $m" >> "$RB/errors.log"; return 1; fi
  # POLICY (driver3): try1 at CEIL (9000 MB); on failure the retry ("try16") runs ALONE at CEIL_RETRY (16000 MB; watchdog kills at 90% = 14400 MB).
  # cls ALONE_RETRY16 = the module already has a FAIL row try1/try2 (e.g. GD3O265): only the 16 GB attempt is made.
  local tries="1 16"; [ "$cls" = ALONE_RETRY16 ] && tries="16"
  for try in $tries; do
    c=$CEIL; [ $try = 16 ] && { c=$CEIL_RETRY; alone=1; }
    if [ $alone = 1 ] && [ -z "$HAVE_ALONE" ]; then become_alone "$L" "$m" "$c" || return 2; fi
    if [ $try = 16 ]; then   # we are alone now: foreign lean RSS gate (never touch foreign processes; guard kills at 20 GB total)
      local fo; fo=$(live_foreign)
      if [ $((fo + c)) -gt $RETRY_FOREIGN_CAP_MB ]; then
        echo "$(date +%T) lane $L: DEFER 16 GB retry of $m: foreign lean ${fo} MB + $c > $RETRY_FOREIGN_CAP_MB; retry again in 10 min" | tee -a "$RB/FAILURES.md" >> "$RB/driver3.out"
        printf '%s\t%s\n' "$m" "$(( $(date +%s) + 600 ))" >> "$LANES/defer.tsv"; rm -f "$SD/$L.cur"; HAVE_ALONE=; return 4
      fi
    fi
    [ $alone = 1 ] && pred_use=$c || pred_use=$pred
    S=$(date +%s); write_cur "$L" "$m" "$pred_use" "$S" "$alone" 0
    rm -f "$LOGD/$nm".out "$LOGD/$nm".err "$LOGD/$nm".watch
    bash "$LAUNCH" "$c" "$LOGD" "$nm" bash -c "cd '$LEAN' && lake build $m" &
    LP=$!; write_cur "$L" "$m" "$pred_use" "$S" "$alone" "$LP"; wait $LP
    W=$(( $(date +%s) - S ))
    if [ -f "$LANES/killed.$L" ] && [ "$(cat "$LANES/killed.$L")" = "$m" ]; then
      rm -f "$LANES/killed.$L"; : > "$LANES/solo/$m"; return 3   # retry-later, no results row
    fi
    peak=$(grep -o 'rss=[0-9]*MB' "$LOGD/$nm.watch" 2>/dev/null | sed 's/rss=//;s/MB//' | sort -n | tail -1); peak=${peak:-NA}
    if grep -q "Build completed successfully" "$LOGD/$nm.out" 2>/dev/null && ! grep -q "WATCHDOG KILL" "$LOGD/$nm.watch" 2>/dev/null \
       && ! grep -q "error:" "$LOGD/$nm.out" "$LOGD/$nm.err" 2>/dev/null; then
      printf '%s\t%s\tOK\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$peak" >> "$RES"; ok=1
      [ $try = 16 ] && echo "$(date +%F\ %T) RETRY16 OK $m wall ${W}s peak ${peak} MB" >> "$RB/FAILURES.md"
      sched_acquire; grep -vxF "$m" "$SD/missing.txt" > "$SD/missing.tmp"; mv "$SD/missing.tmp" "$SD/missing.txt"; sched_release
      [ "$W" -lt 120 ] && rm -f "$LOGD/$nm".out "$LOGD/$nm".err "$LOGD/$nm".watch
      break
    fi
    printf '%s\t%s\tFAIL\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$peak" >> "$RES"
    echo "$(date +%F\ %T) FAIL $m try$try ceiling ${c} MB wall ${W}s peak ${peak} MB (log $LOGD/$nm.*)" >> "$RB/FAILURES.md"
    cp "$LOGD/$nm.watch" "$LOGD/$nm.try$try.watch" 2>/dev/null
    rm -f "$SD/$L.cur"; HAVE_ALONE=
  done
  [ $ok = 1 ] && return 0
  echo "$(date +%T) FAIL $m (log $LOGD/$nm.*)" >> "$RB/errors.log"; return 1
}
# claim_alone LANE MOD PRED: wait until the other lane is idle, then (under the sched lock) write our alone cur file and drop want_alone, atomically.
claim_alone() {
  local L=$1
  while :; do
    sched_acquire
    if [ -z "$(others_cur "$L")" ]; then write_cur "$L" "$2" "$3" "$(date +%s)" 1 0; rm -f "$SD/want_alone.$L"; sched_release; return 0; fi
    sched_release; sleep 5
  done
}
# become_alone LANE MOD CEIL: announce want_alone (blocks other admissions), release our own cur, then claim_alone.
become_alone() {
  local L=$1
  sched_acquire; echo "$2" > "$SD/want_alone.$L"; rm -f "$SD/$L.cur"; sched_release
  claim_alone "$L" "$2" "$3"; HAVE_ALONE=1; return 0
}

lane() {
  local L=$1 LK=$P/private/logs/LEAN_SLOT.lock; [ "$L" = B ] && LK=$P/private/logs/LEAN_SLOT2.lock
  SD=$LANES; RESF=$RES; EXTRA=; DRY=; DRYLIVE=
  while :; do
    stopfile && { echo "$(date +%T) lane $L: stop file present; exiting" >> "$RB/driver3.out"; break; }
    [ "$(free_gb)" -ge $DISK_STOP_GB ] || { echo "$(date +%T) lane $L: disk below $DISK_STOP_GB GB; stopping" >> "$RB/driver3.out"; break; }
    if ! mkdir "$LK" 2>/dev/null; then sleep 15; continue; fi
    sched_acquire
    decide "$L"
    case "$D_RES" in
      TAKE|ALONEWAIT)
        if ! mkdir "$LANES/claims/$D_MOD" 2>/dev/null; then sched_release; rmdir "$LK"; sleep 3; continue; fi
        echo "lane $L pid $$ building $D_MOD" > "$LK/owner"
        echo "$(date +%T) lane $L $D_RES $D_MOD pred=$D_PRED cls=$D_CLS :: $D_WHY" >> "$RB/driver3.out"
        local cls=$D_CLS m=$D_MOD pred=$D_PRED ceil=$D_CEIL
        if [ "$D_RES" = TAKE ]; then write_cur "$L" "$m" "$pred" "$(date +%s)" "$([ "$cls" != NORMAL ] && echo 1 || echo 0)" 0; else echo "$m" > "$SD/want_alone.$L"; fi
        sched_release
        HAVE_ALONE=; [ "$D_RES" = TAKE ] && [ "$cls" != NORMAL ] && HAVE_ALONE=1
        [ "$D_RES" = ALONEWAIT ] && { claim_alone "$L" "$m" "$pred"; HAVE_ALONE=1; }
        run_module "$L" "$m" "$pred" "$cls" "$ceil"; rc=$?
        rm -f "$SD/$L.cur" "$SD/want_alone.$L"; rm -rf "$LANES/claims/$m"
        echo "$(date +%T) lane $L finished $m rc=$rc" >> "$RB/driver3.out"
        rm -f "$LK/owner"; rmdir "$LK" 2>/dev/null
        ;;
      DONE) sched_release; rm -f "$LK/owner"; rmdir "$LK" 2>/dev/null; echo "$(date +%T) lane $L: nothing left ($D_WHY)" >> "$RB/driver3.out"; break ;;
      *) sched_release; rm -f "$LK/owner"; rmdir "$LK" 2>/dev/null
         echo "$(date +%T) lane $L WAIT :: $D_WHY" >> "$RB/driver3.log"
         local k=0; while [ $k -lt 4 ]; do stopfile && break; sleep 5; k=$((k+1)); done ;;
    esac
  done
}

# ---------- modes ----------
if [ "$MODE" = --test-monitor ]; then   # fake launchers (sleep) in a scratch lanes dir; threshold forced low; nothing real is killed
  LANES=$RB/lanes_test; rm -rf "$LANES"; mkdir -p "$LANES"; ERRLOG=$LANES/errors.log; KILL_MB=100; PAUSE_S=600
  sleep 300 & OLD=$!; sleep 300 & NEW=$!; N=$(date +%s)
  printf 'mod.old\t6000\t%s\t0\t%s\n' "$((N-100))" "$OLD" > "$LANES/A.cur"; printf 'mod.new\t6000\t%s\t0\t%s\n' "$N" "$NEW" > "$LANES/B.cur"
  echo "live ours now: $(live_ours) MB (threshold $KILL_MB)"; monitor & MP=$!; sleep 7; kill $MP 2>/dev/null
  echo "killed markers: $(ls "$LANES" | grep '^killed' | tr '\n' ' ') -> $(cat "$LANES"/killed.* 2>/dev/null)"
  echo "OLD alive: $(kill -0 $OLD 2>/dev/null && echo yes || echo NO)   NEW alive: $(kill -0 $NEW 2>/dev/null && echo yes || echo no)"
  echo "pause_until: $(cat "$LANES/pause_until" 2>/dev/null) (now $(date +%s))"; cat "$LANES/retry.log"; kill $OLD $NEW 2>/dev/null; rm -rf "$LANES"; exit 0
fi

if [ "$MODE" = --mkdag ]; then bash "$RB/mkdag.sh"; wc -l "$DAG"; exit 0; fi

if [ "$MODE" = --test-dag ]; then
  echo "full DAG (source parse) vs MANIFEST project_imports, all rows:"
  awk -F'\t' 'function srt(s,  n,a,i,j,t,r){n=split(s,a,","); for(i=1;i<=n;i++)for(j=i+1;j<=n;j++)if(a[j]<a[i]){t=a[i];a[i]=a[j];a[j]=t}; r=""; for(i=1;i<=n;i++)if(a[i]!="")r=r a[i] ","; return r}
    NR==FNR{ if(FNR>1) mi[$2]=srt($10); next } { if (srt($2)!=mi[$1]) bad++; tot++ } END{print "rows",tot,"mismatches",bad+0}' "$MAN" "$DAG"
  echo "20 random modules vs lean --deps:"; bad=0
  cd "$LEAN"; for m in $(awk -F'\t' 'NR>1{print $2}' "$MAN" | awk -v sd=$RANDOM 'BEGIN{srand(sd)}{print rand()"\t"$0}' | sort -n | head -20 | cut -f2); do
    p=$(awk -F'\t' -v m=$m '$2==m{print $3}' "$MAN")
    a=$(lake env lean --deps "$p" 2>/dev/null | grep -o 'LRSpectrumFull/[^ ]*\.olean' | sed 's#/#.#g; s#\.olean$##' | sort | tr '\n' ',')
    b=$(awk -F'\t' -v m=$m '$1==m{print $2}' "$DAG" | tr ',' '\n' | sort | tr '\n' ',' | sed 's/^,//')
    [ "$a" = "$b" ] || { bad=$((bad+1)); echo "MISMATCH $m"; }
  done; echo "mismatches=$bad"; exit 0
fi

if [ "$MODE" = --dryrun ]; then
  STEPS=${2:-24}
  SDX=$RB/lanes_dry; rm -rf "$SDX"; mkdir -p "$SDX/claims" "$SDX/solo"; SD=$SDX; DRY=1
  RESF=$SDX/results.sim; cp "$RES" "$RESF"; EXTRA=$SDX/extra.sim; : > "$EXTRA"
  FROM=${3:-0}; [ "$FROM" -gt 0 ] && awk -F'\t' -v f=$FROM 'NR>1 && $1+0<f{print $2}' "$MAN" > "$EXTRA"   # pretend every module with manifest idx < FROM is built
  cur=; [ -f "$P/private/logs/LEAN_SLOT.lock/owner" ] && cur=$(sed 's/.* building //' "$P/private/logs/LEAN_SLOT.lock/owner")
  echo "dry run: real running module = ${cur:-none}; live ours now $(live_ours) MB, foreign $(live_foreign) MB, free disk $(free_gb) GB"
  if [ -n "$cur" ]; then mkdir "$SDX/claims/$cur"; write_cur A "$cur" 6000 "$(date +%s)" 0 0; fi
  NOW0=$(date +%s)
  simnow=0
  for step in $(seq 1 $STEPS); do
    for L in B A; do
      [ -e "$SDX/$L.cur" ] || [ -e "$SDX/want_alone.$L" ] && continue
      DRYLIVE=0; for f in $SDX/*.cur; do [ -f "$f" ] && DRYLIVE=$((DRYLIVE + $(cut -f2 "$f")*100/115*85/100)); done; DRYFREE=$(free_gb)
      decide "$L"
      echo "step $step lane $L: $D_RES ${D_MOD:+$D_MOD pred=$D_PRED cls=$D_CLS} :: $D_WHY"
      if [ "$D_RES" = TAKE ]; then mkdir "$SDX/claims/$D_MOD"; write_cur "$L" "$D_MOD" "$D_PRED" "$((NOW0+step))" "$([ "$D_CLS" != NORMAL ] && echo 1 || echo 0)" 0; fi
      if [ "$D_RES" = ALONEWAIT ]; then echo "      -> $L would claim $D_MOD, block other admissions, and wait for the other lane to finish"; mkdir "$SDX/claims/$D_MOD"; echo "$D_MOD" > "$SDX/want_alone.$L"; fi
    done
    # complete the oldest running module (simulated OK with peak = pred/1.15)
    oldest=; os=99999999999; for f in $SDX/*.cur; do [ -f "$f" ] || continue; s=$(cut -f3 "$f"); [ "$s" -le "$os" ] && { os=$s; oldest=$f; }; done
    if [ -n "$oldest" ]; then mm=$(cut -f1 "$oldest"); pd=$(cut -f2 "$oldest"); echo "$mm" >> "$EXTRA"
      echo "         (sim) $mm finishes"; rm -f "$oldest"; rm -rf "$SDX/claims/$mm"
      for w in $SDX/want_alone.*; do [ -f "$w" ] || continue; wl=${w##*.}; wm=$(cat $w); if [ -z "$(others_cur $wl)" ]; then write_cur "$wl" "$wm" 9000 "$((NOW0+step))" 1 0; rm -f "$w"; echo "         (sim) lane $wl now runs $wm alone"; fi; done
    else echo "         (sim) nothing running"; fi
  done
  rm -rf "$SDX"; exit 0
fi

# ---------- run ----------
SD=$LANES
if ps -axo command= | grep -E 'bin/lean ' | grep -q 'rebuild_five/checkout'; then echo "a lean of ours is already running; refusing to start (stop driver.sh first via STOP)" >&2; exit 4; fi
ps -axo pid=,command= | awk -v me=$$ -v pp=$PPID '$1!=me && $1!=pp && /rebuild_five\/driver[23]?\.sh/ && !/awk/ {f=1} END{exit !f}' && { echo "another driver is running" >&2; exit 5; }
echo $$ > "$RB/driver3.pid"
rm -rf "$LANES/claims" "$LANES/sched.lock" "$LANES"/*.cur "$LANES"/want_alone.* "$LANES"/killed.* "$LANES"/pause_until; mkdir -p "$LANES/claims" "$LANES/solo"
rm -rf "$P/private/logs/LEAN_SLOT2.lock"
[ -s "$DAG" ] || bash "$RB/mkdag.sh"
# startup sweep: OK rows whose .olean is absent are not trusted (rebuilt), recorded in missing.txt
find "$LEAN/.lake/build/lib/lean/LRSpectrumFull" -name '*.olean' 2>/dev/null | sed "s#^$LEAN/.lake/build/lib/lean/##; s#\.olean\$##; s#/#.#g" | sort > "$LANES/have_olean.txt"
awk -F'\t' '$3=="OK"{print $1}' "$RES" | sort -u | comm -23 - "$LANES/have_olean.txt" > "$LANES/missing.txt"
echo "$(date +%T) driver3 start pid $$; OK rows without olean: $(wc -l < "$LANES/missing.txt")" >> "$RB/driver3.out"
status
monitor & MONPID=$!
( lane A ) & LA=$!
sleep 45   # stagger: lane A takes its first module before lane B looks
( lane B ) & LB=$!
while kill -0 $LA 2>/dev/null || kill -0 $LB 2>/dev/null; do
  sleep 15; [ $(( $(date +%s) - LASTST )) -ge 300 ] && status
done
kill $MONPID 2>/dev/null; status
echo "$(date +%T) driver3 finished: $(tail -1 "$RB/STATUS.md")" >> "$RB/errors.log"
echo FINISHED3 > "$RB/driver.finished"
