#!/bin/bash
# janitor.sh (orchestrator 2026-11-21): deletes <Module>.setup.json files (about 1.8 MB each; 17,598 modules would be ~30 GB) older than 20 minutes in the rebuild checkout only.
# Tested 2026-11-21 23:5x: with one setup.json deleted, `lake build --no-build <module>` still says 'All targets up-to-date'. Stop: touch rebuild_five/JANITOR_STOP
B=/PATH/TO/programme/private/rebuild_five/checkout/lean/.lake/build/ir
S=/PATH/TO/programme/private/rebuild_five/JANITOR_STOP
L=/PATH/TO/programme/private/rebuild_five/janitor.log
while [ ! -f $S ]; do
  N=$(find $B -name '*.setup.json' -mmin +20 2>/dev/null | wc -l | tr -d ' ')
  find $B -name '*.setup.json' -mmin +20 -delete 2>/dev/null
  echo "$(date '+%F %T') deleted $N setup.json files; disk free $(df -k /PATH/TO | tail -1 | awk '{printf "%.2f GB",$4/1048576}')" >> $L
  sleep 300
done
