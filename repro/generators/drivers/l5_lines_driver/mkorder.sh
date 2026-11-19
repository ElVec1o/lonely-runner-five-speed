#!/bin/bash
# mkorder.sh : writes order.txt (idx module kind node points) for the CID-MODE plan (chunks LinRQSC<j> = consecutive class ids, plan order = class table order).
# BUILD order (independent of the table order): LinRCov, chunks by ascending visited points (cheap first, heavy last), then the group / node assembly
# modules in asm_order, LinRAll, LinRFinal.
. /DEV_TREE/work/l5_lines_driver/common.sh
{ printf "0\tLinRCov\tcov\t-\t0\n"
  sort -t$'\t' -k5,5n -k6,6n $PLAN | awk -F'\t' -v OFS='\t' '{print NR, $1, "chunk", $2, $5}'
  N=$(wc -l < $PLAN)
  awk -F'\t' -v OFS='\t' -v n=$((N+1)) '$1 != "all" {print n++, $2, "asm", $1, 0} END {print n++, "LinRAll", "asm", "all", 0; print n++, "LinRFinal", "final", "-", 0}' $RO/src_asm/asm_order.txt
} > $RO/order.txt
wc -l $RO/order.txt
