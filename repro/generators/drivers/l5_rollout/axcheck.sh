#!/bin/bash
# axcheck.sh OUTFILE QUALIFIED_NAME_SUFFIX   e.g.  axcheck.sh logs/mod/GD3O124.out N124.t3_nodeU
# prints "STD [..]" when the `#print axioms` line of the theorem lists only propext, Classical.choice, Quot.sound; "BAD [..]" when anything else
# (sorryAx, native_decide axioms, new axioms); "NOLINE" when the line is absent.  Exit 0 only for STD.
F=$1; N=$2
LINE=$(grep -F ".${N}' depends on axioms:" "$F" 2>/dev/null | head -1)
[ -z "$LINE" ] && { echo "NOLINE"; exit 2; }
AX=$(echo "$LINE" | sed 's/.*depends on axioms: \[\(.*\)\].*/\1/')
BAD=0
OLDIFS=$IFS; IFS=','
for a in $AX; do
  a=$(echo "$a" | sed 's/^ *//;s/ *$//')
  case "$a" in propext|Classical.choice|Quot.sound) ;; *) BAD=1;; esac
done
IFS=$OLDIFS
if [ $BAD = 0 ]; then echo "STD [$AX]"; exit 0; else echo "BAD [$AX]"; exit 1; fi
