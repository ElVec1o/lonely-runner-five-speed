#!/bin/bash
# usage: run.sh MODULE_SUFFIX   e.g. run.sh L5WP1.BoxCore   (builds LRSpectrumFull.<suffix> via the one-off wrapper)
# Guards: foreign lean RSS < 9 GB, disk >= 3 GB, no lean/lake of ours running.  One build at a time.  CEIL default 12000.
M=${1:?}; P=/DEV_TREE; L=$P/work/lean5_wp1/logs
F=$(ps -Ao rss,comm | awk '/lean/{s+=$1} END{printf "%.2f", s/1048576}')
DG=$(df -g /System/Volumes/Data | awk 'NR==2{print $4}')
echo "PRE foreign_lean_rss_GB=$F disk_free_GB=$DG $(date +%T)"
awk -v f="$F" 'BEGIN{exit !(f<9)}' || { echo "REFUSED: foreign lean RSS $F GB >= 9"; exit 4; }
[ "$DG" -ge 3 ] || { echo "REFUSED: disk $DG GB"; exit 5; }
N=$(echo "$M" | tr '.' '_'); rm -f $L/$N.out $L/$N.err $L/$N.watch
S=$(date +%s)
bash $P/logs/rqlean/launch_oneoff_6000.sh ${CEIL:-12000} $L $N bash -c "cd $P/lean && /usr/bin/time -l lake build LRSpectrumFull.$M"
E=$(date +%s)
echo "POST wall=$((E-S))s"
tail -2 $L/$N.watch
echo "peak_tree_rss_MB=$(grep -o 'rss=[0-9]*' $L/$N.watch | cut -d= -f2 | sort -n | tail -1)"
grep -E "maximum resident|real" $L/$N.err
tail -${TAILN:-6} $L/$N.out
