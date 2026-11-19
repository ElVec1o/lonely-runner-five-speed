#!/bin/bash
# usage: batch.sh M1 M2 ...   builds the modules one after the other (each only after the previous finished), waiting for foreign lean RSS < 8 GB
cd /DEV_TREE/work/lean5_wp1
for m in "$@"; do
  until [ "$(ps -Ao rss,comm | awk '/lean/{s+=$1} END{print (s/1048576<8)}')" = 1 ]; do sleep 10; done
  echo "== $m"; CEIL=${CEIL:-12000} bash run.sh L5WP1.$m 2>&1 | grep -E "POST|peak_tree|real|maximum|error|REFUSED|exit"; grep -E "error" -A8 logs/L5WP1_$m.out 2>/dev/null | head -40; grep -E "axioms|depends on|sorryAx" logs/L5WP1_$m.out 2>/dev/null | head -4
done; echo BATCH_DONE
