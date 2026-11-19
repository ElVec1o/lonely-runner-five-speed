#!/bin/bash
# regen.sh : rebuild results.tsv from state/*.row (atomic).  Columns:
# idx module kind node points status cpu_s peak_MB guard_kills wall_s axioms started finished note
. /DEV_TREE/work/l5_lines_driver/common.sh
{ printf "idx\tmodule\tkind\tnode\tpoints\tstatus\tcpu_s\tpeak_MB\tguard_kills\twall_s\taxioms\tstarted\tfinished\tnote\n"
  cat $RO/state/*.row 2>/dev/null | sort -t$'\t' -k1,1n; } > $RO/results.tsv.tmp && mv $RO/results.tsv.tmp $RO/results.tsv
