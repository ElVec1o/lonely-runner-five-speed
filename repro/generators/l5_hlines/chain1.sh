#!/bin/bash
# chain1.sh : S4W bisect, probes run one at a time (stop: l5_hlines/STOPW)
H=/DEV_TREE/work/l5_hlines
P=/DEV_TREE/logs/l5s4w/probes
for X in "$@"; do
  [ -f $H/STOPW ] && { echo "STOPW"; exit 0; }
  bash $H/probe.sh $X $P/$X.lean
done
