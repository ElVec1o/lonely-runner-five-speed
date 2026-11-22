#!/bin/bash
# Resumable one-lane rebuild driver for the PUBLIC five-speed archive (fresh checkout). Bash only.
# Reads checkout/repro/MANIFEST.tsv (topological order, col 9 = project imports). One `lake build <module>` per module,
# through the one-off launcher (watchdog 90% of ceiling). Results: results.tsv (module sha256 status try wall_s peak_MB).
# Stops cleanly (after the current module) when rebuild_five/STOP or programme/NEXT_BIG/PAUSE exists.
P=/PATH/TO/programme
RB=$P/private/rebuild_five
CK=$RB/checkout
LEAN=$CK/lean
MAN=$CK/repro/MANIFEST.tsv
RES=$RB/results.tsv
LOGD=$RB/logs
LAUNCH=$P/private/logs/rqlean/launch_oneoff_6000.sh
LOCK=$P/private/logs/LEAN_SLOT.lock
CKPT=$P/NEXT_BIG/H_rebuild/CHECKPOINT.md
CEIL=${CEIL:-9000}; CEIL_RETRY=${CEIL_RETRY:-12000}
mkdir -p "$LOGD" "$P/NEXT_BIG/H_rebuild"
[ -f "$RES" ] || printf 'module\tsha256\tstatus\ttry\twall_s\tpeak_MB\n' > "$RES"
export PATH=$HOME/.elan/bin:$PATH
START_FILE=$RB/driver.start; [ -f "$START_FILE" ] || date +%s > "$START_FILE"
T0=$(cat "$START_FILE")
NTOT=$(($(wc -l < "$MAN")-1))
TOTBYTES=$(awk -F'\t' 'NR>1{s+=$5} END{print s}' "$MAN")
LASTST=0
free_gb() { df -g /System/Volumes/Data | awk 'NR==2{print $4}'; }
leanrss() { ps -axo rss=,command= | grep -E 'bin/lean ' | grep -v grep | awk '{s+=$1} END{print int(s/1024)}'; }
stopfile() { [ -e "$RB/STOP" ] || [ -e "$P/NEXT_BIG/PAUSE" ]; }

status() { # write STATUS.md and CHECKPOINT.md from results.tsv
  local now=$(date +%s) el done fail blocked peak free sumw bytesdone mean eta1 eta2 lastm
  el=$((now-T0))
  done=$(awk -F'\t' '$3=="OK"{d[$1]=1} END{n=0; for(k in d)n++; print n}' "$RES")
  fail=$(awk -F'\t' 'NR>1{s[$1]=$3} END{n=0; for(k in s) if(s[k]=="FAIL")n++; print n}' "$RES")
  blocked=$(wc -l < "$RB/blocked.txt" 2>/dev/null | tr -d ' '); blocked=${blocked:-0}
  peak=$(awk -F'\t' '$3=="OK"&&$6!="NA"&&$6+0>m{m=$6+0; mm=$1} END{print m+0, mm}' "$RES")
  sumw=$(awk -F'\t' '$3=="OK"{s+=$5} END{print s+0}' "$RES")
  bytesdone=$(awk -F'\t' -v resF="$RES" 'BEGIN{while((getline l < resF)>0){split(l,a,"\t"); if(a[3]=="OK")ok[a[1]]=1}} NR>1&&($2 in ok){s+=$5} END{print s+0}' "$MAN")
  free=$(free_gb); lastm=$(tail -1 "$RES" | cut -f1,3,5)
  eta1=NA; eta2=NA
  if [ "$done" -gt 0 ] && [ "$sumw" -gt 0 ]; then
    eta1=$(awk -v s=$sumw -v d=$done -v n=$NTOT 'BEGIN{printf "%.1f h", s/d*(n-d)/3600}')
    eta2=$(awk -v s=$sumw -v b=$bytesdone -v t=$TOTBYTES 'BEGIN{ if(b>0) printf "%.1f h", s/b*(t-b)/3600; else print "NA"}')
  fi
  cat > "$RB/STATUS.md" <<EOF
# REBUILD five-speed v1.0.1 (HEAD $(git -C "$CK" rev-parse --short HEAD)) status $(date '+%F %T')
- modules OK: $done / $NTOT ; failed (latest status FAIL): $fail ; blocked by a failure: $blocked
- elapsed since first launch (wall): $((el/3600)) h $((el%3600/60)) min ; summed module wall time: $sumw s
- ETA (remaining modules x mean wall, optimistic: early modules are small): $eta1 ; ETA (byte-weighted): $eta2 ; QUOTED cost model: about 36.8 h CPU
- max peak RSS of a built module: $peak MB (ceiling $CEIL MB)
- free disk: ${free} GB (stop and checkpoint below 10 GB)
- last result row: $lastm
- driver pid: $(cat "$RB/driver.pid" 2>/dev/null); lean RSS now: $(leanrss) MB
- stop files: $( [ -e "$RB/STOP" ] && echo "STOP present"; [ -e "$P/NEXT_BIG/PAUSE" ] && echo "PAUSE present" )
EOF
  cp "$RB/STATUS.md" "$CKPT"
  LASTST=$now
}

# fail set (modules with latest status FAIL after retry) and blocked set
FAILED=" "; : > "$RB/blocked.txt"
status
i=0
while IFS=$'\t' read -r idx m path h bytes lines kind gen inb imps; do
  [ "$idx" = idx ] && continue
  # published-bytes check
  nm=$(echo "$m" | tr '.' '_')
  if awk -F'\t' -v m="$m" -v h="$h" '$1==m && $2==h && $3=="OK"{f=1} END{exit !f}' "$RES"; then
    ol="$LEAN/.lake/build/lib/lean/$(echo "$path" | sed 's/\.lean$//').olean"
    [ -f "$ol" ] && continue
  fi
  # blocked by a failed import?
  blk=0
  for d in $(echo "$imps" | tr ',' ' '); do case "$FAILED" in *" $d "*) blk=1; break;; esac; done
  if [ $blk = 1 ]; then FAILED="$FAILED$m "; echo "$m" >> "$RB/blocked.txt"; continue; fi
  if stopfile; then echo "$(date +%T) stop file present; stopping before $m"; status; exit 0; fi
  [ "$(free_gb)" -ge 10 ] || { echo "$(date +%T) free disk below 10 GB; checkpointing and stopping before $m"; status; exit 3; }
  src="$LEAN/$path"
  act=$(shasum -a 256 "$src" 2>/dev/null | cut -d' ' -f1)
  if [ "$act" != "$h" ]; then
    printf '%s\t%s\tFAIL\ttry0\t0\tNA\n' "$m" "$h" >> "$RES"; echo "SHA MISMATCH $m" >> "$RB/errors.log"; FAILED="$FAILED$m "; continue
  fi
  try=0; ok=0
  while [ $try -lt 2 ]; do
    try=$((try+1)); c=$CEIL; [ $try = 2 ] && c=$CEIL_RETRY
    while ! mkdir "$LOCK" 2>/dev/null; do sleep 15; stopfile && { echo "stop while waiting for lock"; status; exit 0; }; done
    echo "rebuild_five driver pid $$ building $m" > "$LOCK/owner"
    rm -f "$LOGD/$nm".out "$LOGD/$nm".err "$LOGD/$nm".watch
    S=$(date +%s)
    bash "$LAUNCH" "$c" "$LOGD" "$nm" bash -c "cd '$LEAN' && lake build $m"
    W=$(( $(date +%s) - S ))
    rm -f "$LOCK/owner"; rmdir "$LOCK" 2>/dev/null
    peak=$(grep -o 'rss=[0-9]*MB' "$LOGD/$nm.watch" 2>/dev/null | sed 's/rss=//;s/MB//' | sort -n | tail -1); peak=${peak:-NA}
    if grep -q "Build completed successfully" "$LOGD/$nm.out" 2>/dev/null && ! grep -q "WATCHDOG KILL" "$LOGD/$nm.watch" 2>/dev/null \
       && ! grep -q "error:" "$LOGD/$nm.out" "$LOGD/$nm.err" 2>/dev/null; then
      printf '%s\t%s\tOK\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$peak" >> "$RES"; ok=1
      [ "${W}" -lt 120 ] && rm -f "$LOGD/$nm".out "$LOGD/$nm".err "$LOGD/$nm".watch
      break
    fi
    printf '%s\t%s\tFAIL\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$peak" >> "$RES"
  done
  [ $ok = 1 ] || { FAILED="$FAILED$m "; echo "$(date +%T) FAIL $m (log $LOGD/$nm.*)" >> "$RB/errors.log"; }
  [ $(( $(date +%s) - LASTST )) -ge 300 ] && status
done < "$MAN"
status
echo "$(date +%T) driver finished: $(tail -1 "$RB/STATUS.md")" >> "$RB/errors.log"
echo FINISHED > "$RB/driver.finished"
