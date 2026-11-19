#!/bin/bash
# regen.sh : rebuild results.tsv (one row per rep, atomic mv) from state/<rep>.row; reps without a state row are PENDING.
. /DEV_TREE/work/l5_rollout/common.sh
{
  printf "rep\tstatus\tleaves\tchunks\tnodemods\tmods_built\tcpu_s\tpeak_MB\tguard_kills\twall_s\taxioms\tstarted\tfinished\tnote\n"
  for f in $RO/state/*.row; do [ -f "$f" ] && cat "$f"; done | sort -t$'\t' -k1,1n
} > $RO/results.tsv.tmp
mv $RO/results.tsv.tmp $RO/results.tsv
