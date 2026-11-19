#!/bin/bash
# hl_build.sh [LEVELS]  build the hlines mirror modules AggFive.Hl.* level by level (L leaves, M mids, D roots, T top) through lane_reg.sh (lane 1, 12 GB wrapper).
# A module is built only if every import has an olean not older than its source (an earlier out-of-memory incident) and its own olean is missing/stale.
# Stop file: l5_hlines/STOP (checked between modules).  Log: logs/l5hl/hl_build.log
P=/DEV_TREE
D=$P/work/l5_hlines
LD=$P/logs/l5s4w/hl
SRC=$P/lean
OL=$SRC/.lake/build/lib/lean
mkdir -p $LD
LEVELS=${1:-LMDT}
fresh_import() {   # $1 = module path with slashes (LRSpectrumFull/...): olean exists and is not older than its source
  [ -f "$OL/$1.olean" ] && [ ! "$SRC/$1.lean" -nt "$OL/$1.olean" ]
}
needs_build() {    # $1 = mirror module name (e.g. Leaf0_0): prints BUILD / FRESH / BLOCKED:<import>
  F=$SRC/LRSpectrumFull/AggFive/Hl/$1.lean
  O=$OL/LRSpectrumFull/AggFive/Hl/$1.olean
  NEW=0
  for I in $(grep '^import LRSpectrumFull\.' $F | sed 's/^import //' | tr . /); do
    if ! fresh_import $I; then echo "BLOCKED:$I"; return; fi
    if [ -f "$O" ] && [ "$OL/$I.olean" -nt "$O" ]; then NEW=1; fi
  done
  if [ ! -f "$O" ] || [ "$F" -nt "$O" ] || [ $NEW = 1 ]; then echo BUILD; else echo FRESH; fi
}
for KIND in L M D T; do
  case "$LEVELS" in *$KIND*) ;; *) continue;; esac
  $D/target/release/l5hlines gen 2>>$LD/hl_build.log
  PENDING=""; NB=0; NF=0; NK=0
  for N in $(cat $D/state/hl_order.txt); do
    case $KIND in
      L) case $N in Leaf*) ;; *) continue;; esac;;
      M) case $N in Mid*) ;; *) continue;; esac;;
      D) case $N in D[0-9]*) ;; *) continue;; esac;;
      T) [ "$N" = Top ] || continue;;
    esac
    R=$(needs_build $N)
    case $R in BUILD) PENDING="$PENDING AggFive.Hl.$N"; NB=$((NB+1));; FRESH) NF=$((NF+1));; *) NK=$((NK+1)); echo "$(date +%T) $N $R" >> $LD/hl_blocked.log;; esac
  done
  echo "$(date +%T) level $KIND: build $NB fresh $NF blocked $NK" >> $LD/hl_build.log
  # modules in chunks of 25 per lane call (the lane lock is released between calls)
  set -- $PENDING
  while [ $# -gt 0 ]; do
    [ -f $D/STOPW ] && { echo "$(date +%T) STOP file" >> $LD/hl_build.log; exit 0; }
    B=""; K=0
    while [ $# -gt 0 ] && [ $K -lt 10 ]; do B="$B $1"; shift; K=$((K+1)); done
    bash $D/lane_hl.sh $B >> $LD/hl_lane.log 2>&1
    RC=$?
    echo "$(date +%T) batch of $K rc=$RC first=$(echo $B | cut -d' ' -f1)" >> $LD/hl_build.log
    [ $RC -ne 0 ] && echo "$(date +%T) FAILED batch (continuing)" >> $LD/hl_build.log
  done
done
echo "$(date +%T) hl_build done" >> $LD/hl_build.log
