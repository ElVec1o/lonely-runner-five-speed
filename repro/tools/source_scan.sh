#!/bin/bash
# source_scan.sh : scan ALL manifest sources (17,598; reads the live tree, the omitted generated families included) for constructs that would
# enlarge the trust base.  Comments and docstrings are stripped first (tools/strip_fast.awk).  Prints per-token line counts and file lists
# (to logs/source_scan_files.txt).  Reads sources only; writes only under logs/.
HERE=$(cd "$(dirname "$0")/.." && pwd)
LEAN_DIR=${LEAN_DIR:-$HERE/../lean}
mkdir -p "$HERE/logs"
T=$(mktemp); trap 'rm -f "$T"' EXIT
awk -F'\t' -v d="$LEAN_DIR" 'NR>1{print d "/" $3}' "$HERE/MANIFEST.tsv" | tr '\n' '\0' | xargs -0 awk -f "$HERE/tools/strip_fast.awk" > "$T"
echo "code lines after stripping comments: $(wc -l < "$T") in $(($(wc -l < "$HERE/MANIFEST.tsv")-1)) files"
: > "$HERE/logs/source_scan_files.txt"
for tok in '\bsorry\b' 'native_decide' '^[^:]*:[0-9]+:\s*axiom\b' '\bunsafe\b' 'implemented_by' '@\[extern' '\bopaque\b' 'Classical\.choose' \
           'ofReduceBool' 'trustCompiler' 'skipKernelTC' '\bmacro\b' '\belab\b' '\bsyntax\b' '\bnotation\b' '#eval' 'run_cmd' 'initialize' '\bpartial\b' 'csimp' 'maxHeartbeats' 'set_option'; do
  printf '%-34s lines %s  files %s\n' "$tok" "$(grep -c -E "$tok" "$T")" "$(grep -E "$tok" "$T" | cut -d: -f1 | sort -u | wc -l | tr -d ' ')"
  grep -E "$tok" "$T" | cut -d: -f1 | sort -u | sed "s|^$LEAN_DIR/||; s|^|$tok\t|" >> "$HERE/logs/source_scan_files.txt"
done
echo "decide +kernel lines: $(grep -c 'decide +kernel' "$T")"
