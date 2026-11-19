#!/bin/bash
# build.sh : validate the plan for, or build, the 17,598 project modules of the five-speed headline theorems, ONE MODULE AT A TIME, in the order of MANIFEST.tsv.
#
#   NEVER run a bare `lake build` for this project (lake starts one lean worker per core, each 4-10 GB, so a whole-tree
#   build can use tens of GB and exhaust a 24 GB machine).  `lake` here (5.0.0 / Lean 4.30.0) has NO -j flag.  This script builds exactly
#   one module per `lake build LRSpectrumFull.<Module>` call, after all of that module's project imports are known to be built, with one
#   lean process at a time.  A FROM-SCRATCH RUN OF --run IS ABOUT 36.8 h OF LEAN TIME (leaf-rollout cost model, QUOTED, NOT measured end to end)
#   plus lake start-up per call (OBSERVED 1-10 s per module for already-built modules); it was NOT performed for this bundle.
#
# MODES (exactly one)
#   --plan          validate, no lake, no lean: manifest readable, toolchain / Mathlib pins, every in_bundle=yes source present with the
#                   manifest sha256, every omitted generated source (in_bundle=no) either present with the right sha256 or reported missing
#                   (run `regen_data.sh --full --install --steps build,v3,s4o,lines` first), order topological, free disk.  Exit 0 valid; 2 invalid; 4 only the omitted
#                   generated families are missing or differ.
#   --status        --plan, then ONE `lake build --no-build LRSpectrumFull.L5S5.FiveSpeedFinal4` (reports `All targets up-to-date (N jobs)` on a built tree)
#   --status-each   --plan, then one `lake build --no-build` per selected module (up to 17,598 sequential lake calls: slow; use with --from/--to/--only)
#   --run           build the selected modules (resumable; see below)
#   --by-group      print module counts and manifest index ranges by directory (no lake) and exit
# OPTIONS
#   --from N --to N      select manifest indices N..M (default all)
#   --only A,B,...       select modules by name (the leading `LRSpectrumFull.` may be omitted)
#   --force              --run: build even if the results table has an OK row with the same sha256
#   --results FILE       results table (default logs/build_results.tsv); rows: module sha256 status try wall_s peak_MB
#   --retries N          guard-killed builds (exit 137, no error line) are retried N times (default 6) after --retry-wait S (default 600)
# ENVIRONMENT (defaults in brackets)
#   LEAN_DIR       the Lean project root (the lean/ directory of this repository)  [$HERE/../lean]
#   CEILING_MB     memory ceiling handed to the wrapper                [9000]  (watchdog kills the process tree at 90 %)
#   WRAPPER        launcher `WRAPPER CEILING LOGDIR NAME cmd...` writing `rss=NNNMB` lines to LOGDIR/NAME.watch [none: plain run, no watchdog (not recommended)]
#   GATE_RESERVE_MB / GATE_LIMIT_MB   wait while (RSS of all lean processes + RESERVE) > LIMIT   [9500 / 18000]
#   LOCK           atomic lock directory (mkdir)                       [./logs/build.lock]
#   DISK_FLOOR_GB  abort below this many free GB                       [3]
#   ASSUME_BUILT=1 skip the "imports are built" pre-check (use when the tree was built by other means, e.g. an incrementally built tree)
#
# RESUMABLE: after each module one row goes to the results table; a second --run skips modules with an OK row and the same sha256.
# ABORTS on a real `error:` line or on a kill by its own watchdog (later modules would import an unbuilt module and lake would then rebuild the
# unbuilt imports in parallel).  Guard / OOM kills (exit 137, no error line) are retried.
# EXIT: 0 done (or plan valid); 1 real error / abort; 2 plan invalid; 3 disk / lock problem; 4 omitted generated sources missing.

HERE=$(cd "$(dirname "$0")" && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
CEILING_MB=${CEILING_MB:-9000}
GATE_RESERVE_MB=${GATE_RESERVE_MB:-9500}
GATE_LIMIT_MB=${GATE_LIMIT_MB:-18000}
DISK_FLOOR_GB=${DISK_FLOOR_GB:-3}
if [ -z "${WRAPPER+x}" ]; then WRAPPER=""; fi
if [ -z "${LOCK+x}" ]; then LOCK=$HERE/logs/build.lock; fi
PIN_TOOLCHAIN="leanprover/lean4:v4.30.0"
PIN_MATHLIB_REV="c5ea00351c28e24afc9f0f84379aa41082b1188f"
ROOT=LRSpectrumFull.L5S5.FiveSpeedFinal4
MANIFEST=${MANIFEST:-$HERE/MANIFEST.tsv}
LOGDIR=$HERE/logs/build
RESULTS=$HERE/logs/build_results.tsv
MODE=""; FROM=1; TO=100000; ONLY=""; FORCE=0; RETRIES=6; RETRY_WAIT=600

while [ $# -gt 0 ]; do
  case "$1" in
    --plan|--status|--status-each|--run) MODE=${1#--} ;;
    --by-group) MODE=bygroup ;;
    --from) FROM=$2; shift ;;
    --to) TO=$2; shift ;;
    --only) ONLY=$2; shift ;;
    --force) FORCE=1 ;;
    --results) RESULTS=$2; shift ;;
    --retries) RETRIES=$2; shift ;;
    --retry-wait) RETRY_WAIT=$2; shift ;;
    -h|--help) sed -n '2,45p' "$0"; exit 0 ;;
    *) echo "unknown option $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done
[ -n "$MODE" ] || { echo "give one of --plan --status --status-each --run --by-group (see --help)" >&2; exit 2; }
mkdir -p "$LOGDIR" "$(dirname "$RESULTS")"
[ -f "$MANIFEST" ] || { echo "MANIFEST.tsv not found: $MANIFEST" >&2; exit 2; }
T=$(mktemp -d)

# ---- selection (awk, one pass): $T/sel.tsv = idx module path sha in_bundle imports for the selected rows --------------------------
awk -F'\t' -v from="$FROM" -v to="$TO" -v only="$ONLY" '
  BEGIN { n = split(only, w, ","); for (i = 1; i <= n; i++) { s = w[i]; if (s !~ /^LRSpectrumFull\./) s = "LRSpectrumFull." s; want[s] = 1 } }
  NR > 1 && $1 >= from && $1 <= to && (only == "" || ($2 in want)) { print $1 "\t" $2 "\t" $3 "\t" $4 "\t" $9 "\t" $10; found[$2] = 1 }
  END { for (s in want) if (!(s in found)) { print "ONLY-NOT-FOUND " s > "/dev/stderr" } }' "$MANIFEST" > "$T/sel.tsv" || exit 2
NTOT=$(($(wc -l < "$MANIFEST")-1)); NSEL=$(wc -l < "$T/sel.tsv" | tr -d ' ')
[ "$NSEL" -gt 0 ] || { echo "no module selected" >&2; exit 2; }
echo "manifest: $NTOT modules ($MANIFEST); selected $NSEL"

if [ "$MODE" = bygroup ]; then
  awk -F'\t' 'NR>1{ p=$3; sub(/^LRSpectrumFull\//,"",p); g=p; if (g ~ /\//) { sub(/\/[^\/]*$/,"",g) } else g="(top level)"; n[g]++; b[g]+=$5; if (!(g in first)) first[g]=$1; last[g]=$1 }
        END{ for (g in n) printf "%-16s modules %6d  bytes %11d  manifest idx %5d..%5d\n", g, n[g], b[g], first[g], last[g] }' "$MANIFEST" | sort -k7 -n
  exit 0
fi

free_gb() { df -Pk "$LEAN_DIR" | awk 'NR==2{print int($4/1048576)}'; }
leanrss() { ps -axo rss=,command= | grep -E 'bin/lean ' | grep -v grep | awk '{s+=$1} END{print int(s/1024)}'; }

# ---- PLAN ---------------------------------------------------------------------------------------------------------------------
BAD=0; REGEN=0
echo "---- plan validation ----"
if [ "$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null)" = "$PIN_TOOLCHAIN" ]; then echo "ok   lean-toolchain = $PIN_TOOLCHAIN"; else echo "FAIL lean-toolchain is '$(cat "$LEAN_DIR/lean-toolchain" 2>/dev/null)', expected $PIN_TOOLCHAIN"; BAD=1; fi
if grep -q "\"rev\": \"$PIN_MATHLIB_REV\"" "$LEAN_DIR/lake-manifest.json" 2>/dev/null; then echo "ok   lake-manifest.json pins mathlib $PIN_MATHLIB_REV"; else echo "FAIL lake-manifest.json does not pin mathlib $PIN_MATHLIB_REV"; BAD=1; fi
# present files -> sha256 in one batch
awk -F'\t' -v d="$LEAN_DIR" '{ print d "/" $3 }' "$T/sel.tsv" | while IFS= read -r f; do [ -f "$f" ] && printf '%s\0' "$f"; done | xargs -0 shasum -a 256 2>/dev/null > "$T/have.sha"
awk -F'\t' -v d="$LEAN_DIR" -v haveF="$T/have.sha" '
  BEGIN { while ((getline l < haveF) > 0) { split(l, a, "  "); have[a[2]] = a[1] } }
  { f = d "/" $3
    if (!(f in have)) { if ($5 == "yes") { print "FAIL missing source " $3; bad++ } else { miss++ } }
    else if (have[f] != $4) { if ($5 == "yes") { print "FAIL sha256 differs: " $2; bad++ } else { dif++ } }
  }
  END { printf "RESULT %d %d %d\n", bad+0, miss+0, dif+0 }' "$T/sel.tsv" > "$T/plan.out"
grep -E '^FAIL' "$T/plan.out" | head -20
read -r _ bad miss dif <<< "$(grep '^RESULT' "$T/plan.out")"
[ "${bad:-1}" = 0 ] || BAD=1
{ [ "${miss:-0}" = 0 ] && [ "${dif:-0}" = 0 ]; } || REGEN=1
# a full-manifest order check (independent of the selection)
OV=$(awk -F'\t' 'NR==FNR{if(FNR>1)idx[$2]=$1; next} FNR>1{n=split($10,a,","); for(j=1;j<=n;j++) if(a[j]!="" && !(a[j] in idx && idx[a[j]]<$1)) c++} END{print c+0}' "$MANIFEST" "$MANIFEST")
echo "selected $NSEL modules; in-bundle problems $bad; omitted generated sources missing $miss, different $dif; order violations in the manifest $OV"
[ "$OV" = 0 ] || BAD=1
DG=$(free_gb); if [ "$DG" -ge "$DISK_FLOOR_GB" ]; then echo "ok   free disk ${DG} GB >= floor ${DISK_FLOOR_GB} GB"; else echo "FAIL free disk ${DG} GB < floor ${DISK_FLOOR_GB} GB"; BAD=1; fi
echo "machine: lean RSS now $(leanrss) MB (gate: wait while RSS + $GATE_RESERVE_MB > $GATE_LIMIT_MB); wrapper='${WRAPPER:-none}'; lock=$LOCK; ceiling=$CEILING_MB MB"
echo "cost: from-scratch --run = about 36.8 h of Lean time (QUOTED leaf-rollout cost model; not measured end to end) + 1-10 s lake start-up per module (OBSERVED on a built tree)"
if [ $BAD != 0 ]; then echo "PLAN INVALID"; rm -rf "${T:?}"; exit 2; fi
if [ $REGEN != 0 ]; then
  echo "PLAN INCOMPLETE: the omitted generated families (l5s4o GD3O*, l5qemit LinRQSC*) are not (all) present or differ: run regen_data.sh --full --install --steps build,v3,s4o,lines"
  if [ "$MODE" = plan ]; then rm -rf "${T:?}"; exit 4; fi
else
  echo "PLAN VALID"
  if [ "$MODE" = plan ]; then rm -rf "${T:?}"; exit 0; fi
fi
if [ $REGEN != 0 ] && [ "$ASSUME_BUILT" != 1 ]; then echo "refusing to $MODE with missing generated sources (set ASSUME_BUILT=1 to override for already built selections)"; rm -rf "${T:?}"; exit 4; fi

# ---- STATUS ------------------------------------------------------------------------------------------------------------------
cd "$LEAN_DIR" || exit 2
if [ "$MODE" = status ]; then
  echo "---- lake build --no-build $ROOT ----"
  lake build --no-build "$ROOT" 2>&1 | tail -3
  rm -rf "${T:?}"; exit 0
fi
if [ "$MODE" = status-each ]; then
  NUP=0; NNB=0
  while IFS=$'\t' read -r idx mod path sha inb imps; do
    if lake build --no-build "$mod" > "$LOGDIR/status_$(echo "$mod" | tr '.' '_').out" 2>&1; then echo "UP-TO-DATE  $mod"; NUP=$((NUP+1)); else echo "NEEDS-BUILD $mod"; NNB=$((NNB+1)); fi
  done < "$T/sel.tsv"
  echo "up-to-date $NUP, needs build $NNB"; rm -rf "${T:?}"; exit 0
fi

# ---- RUN ---------------------------------------------------------------------------------------------------------------------
[ -f "$RESULTS" ] || printf 'module\tsha256\tstatus\ttry\twall_s\tpeak_MB\n' > "$RESULTS"
# pre-check: every project import of a selected module is OK in the results table (same sha256) or selected earlier
if [ "$ASSUME_BUILT" != 1 ]; then
  awk -F'\t' -v resF="$RESULTS" -v manF="$MANIFEST" '
    BEGIN { while ((getline l < manF) > 0) { split(l, a, "\t"); msha[a[1]] = 0; msha[a[2]] = a[4] }
            while ((getline l < resF) > 0) { split(l, a, "\t"); if (a[3] == "OK" && a[2] == msha[a[1]]) ok[a[1]] = 1 } }
    { n = split($6, im, ","); for (j = 1; j <= n; j++) if (im[j] != "" && !(im[j] in ok) && !(im[j] in selbefore)) { print "NOT-BUILT-IMPORT " $2 " <- " im[j]; c++ }
      selbefore[$2] = 1 }
    END { exit (c > 0 ? 1 : 0) }' "$T/sel.tsv" > "$T/pre.out" || { head -5 "$T/pre.out"; echo "ABORT: imports of the selection are not recorded as built in $RESULTS (build from the start, or set ASSUME_BUILT=1)"; rm -rf "${T:?}"; exit 1; }
fi
HELD=0
release() { if [ $HELD = 1 ]; then rm -f "${LOCK:?}/owner" 2>/dev/null; rmdir "$LOCK" 2>/dev/null; HELD=0; fi; }
kill_tree() {  # kill a process and all its descendants (only ours: started by this script)
  local root=$1
  local all=$(ps -axo pid=,ppid= | awk -v r=$root '{pp[$1]=$2} END{t[r]=1; do{c=0; for(p in pp) if(!(p in t) && (pp[p] in t)){t[p]=1;c=1}}while(c); for(p in t) printf "%s ", p}')
  [ -n "$all" ] && kill $all 2>/dev/null
}
WPID=""
on_signal() { echo "signal: stopping our own build tree and releasing our own lock"; [ -n "$WPID" ] && kill_tree "$WPID"; release; exit 1; }
trap on_signal INT TERM
trap 'release; rm -rf "${T:?}"' EXIT
# modules with an OK row of the same sha256 (one awk pass)
awk -F'\t' -v resF="$RESULTS" 'BEGIN { while ((getline l < resF) > 0) { split(l, a, "\t"); if (a[3] == "OK") ok[a[1] "\t" a[2]] = 1 } } { if (($2 "\t" $4) in ok) print $2 }' "$T/sel.tsv" > "$T/done.txt"
NOK=0; NSKIP=0
while IFS=$'\t' read -r idx m path h inb imps; do
  nm=$(echo "$m" | tr '.' '_')
  if [ $FORCE = 0 ] && grep -qxF "$m" "$T/done.txt"; then NSKIP=$((NSKIP+1)); continue; fi
  try=0
  while :; do
    try=$((try+1))
    DG=$(free_gb); [ "$DG" -ge "$DISK_FLOOR_GB" ] || { echo "ABORT: free disk ${DG} GB < floor ${DISK_FLOOR_GB} GB"; exit 3; }
    while [ $(( $(leanrss) + GATE_RESERVE_MB )) -gt "$GATE_LIMIT_MB" ]; do echo "$(date +%T) gate: lean RSS $(leanrss) MB + $GATE_RESERVE_MB > $GATE_LIMIT_MB, waiting before $m"; sleep 30; done
    while ! mkdir "$LOCK" 2>/dev/null; do echo "$(date +%T) lock $LOCK held by '$(cat "$LOCK/owner" 2>/dev/null)', waiting"; sleep 20; done
    HELD=1; echo "build.sh pid $$ building $m" > "$LOCK/owner"
    rm -f "${LOGDIR:?}/${nm:?}.out" "${LOGDIR:?}/${nm:?}.err" "${LOGDIR:?}/${nm:?}.watch"
    S=$(date +%s)
    echo "$(date +%T) build $idx/$NTOT $m (try $try)"
    if [ -n "$WRAPPER" ]; then
      $WRAPPER "$CEILING_MB" "$LOGDIR" "$nm" bash -c "cd '$LEAN_DIR' && lake build $m" &
    else
      ( bash -c "cd '$LEAN_DIR' && lake build $m" > "$LOGDIR/$nm.out" 2> "$LOGDIR/$nm.err" ) &
    fi
    WPID=$!; wait $WPID; WPID=""
    release
    W=$(( $(date +%s) - S ))
    OK=$(grep -c "Build completed successfully" "$LOGDIR/$nm.out" 2>/dev/null)
    PEAK=$(grep -o 'rss=[0-9]*MB' "$LOGDIR/$nm.watch" 2>/dev/null | sed 's/rss=//;s/MB//' | sort -n | tail -1)
    [ -n "$PEAK" ] || PEAK=NA
    if [ "$OK" = "1" ] && ! grep -q "WATCHDOG KILL" "$LOGDIR/$nm.watch" 2>/dev/null; then
      printf '%s\t%s\tOK\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$PEAK" >> "$RESULTS"
      NOK=$((NOK+1)); rm -f "${LOGDIR:?}/${nm:?}.out" "${LOGDIR:?}/${nm:?}.err"; break   # logs are kept only for failures (17,598 modules)
    fi
    printf '%s\t%s\tFAIL\ttry%s\t%s\t%s\n' "$m" "$h" "$try" "$W" "$PEAK" >> "$RESULTS"
    if grep -q "WATCHDOG KILL" "$LOGDIR/$nm.watch" 2>/dev/null; then echo "ABORT: our own watchdog killed $m (peak ${PEAK} MB > 90% of $CEILING_MB MB); not retried blindly"; exit 1; fi
    if grep "error:" "$LOGDIR/$nm.out" "$LOGDIR/$nm.err" 2>/dev/null | grep -qv "code 137"; then
      echo "ABORT: real error in $m (log $LOGDIR/$nm.out):"; grep "error:" "$LOGDIR/$nm.out" "$LOGDIR/$nm.err" | grep -v "code 137" | head -20; exit 1; fi
    if [ "$try" -ge "$RETRIES" ]; then echo "ABORT: $m failed $try times without a real error (external kills); see $LOGDIR/$nm.*"; exit 1; fi
    echo "     guard kill suspected (no error line, exit 137?) at try $try; retry in ${RETRY_WAIT}s"
    sleep "$RETRY_WAIT"
  done
done < "$T/sel.tsv"
echo "DONE: built $NOK, skipped $NSKIP (results: $RESULTS)"
exit 0
