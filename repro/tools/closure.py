#!/usr/bin/env python3
# closure.py ROOT LEAN_DIR : DFS post-order of the LRSpectrumFull.* import closure (thin glue, tiny memory, seconds).
import sys, os, re
root, lean = sys.argv[1], sys.argv[2]
sys.setrecursionlimit(100000)
seen, order, missing = set(), [], []
imp = re.compile(r'^import\s+(\S+)')
def visit(m):
    if m in seen: return
    seen.add(m)
    f = os.path.join(lean, m.replace('.', '/') + '.lean')
    if not os.path.isfile(f):
        missing.append(m); return
    with open(f, encoding='utf-8') as fh:
        for line in fh:
            mm = imp.match(line)
            if mm and mm.group(1).startswith('LRSpectrumFull.'):
                visit(mm.group(1))
    order.append(m)
visit(root)
if missing:
    sys.stderr.write('MISSING: ' + ' '.join(missing) + '\n'); sys.exit(2)
print('\n'.join(order))
