# Compares a screen output of search/tp_screen_par.py (value, degree, polynomial) with exact values for the certificate.
# Usage: python3 -I cmp_screen.py CERT.json SCREEN.json
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import exact_screen as X
X.init(sys.argv[1])
res = json.load(open(sys.argv[2]))
errs = []
for v, d, q in res:
    ex = X.val(q)
    errs.append((v - ex, v, ex, d, q))
errs.sort(key=lambda t: t[0])
print('n', len(errs), 'min err %.3e max err %.3e' % (errs[0][0], errs[-1][0]))
for t in errs[:5] + errs[-5:]:
    print('  err %+.3e screen %+.4e exact %+.4e deg %d %s' % t)
import collections
by = collections.defaultdict(list)
for t in errs: by[t[3]].append(abs(t[0]))
for d in sorted(by): print('deg', d, 'n', len(by[d]), 'max |err| %.2e' % max(by[d]))
