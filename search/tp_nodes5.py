# a5 nodes: targeted refinement where the a3 diagnostic located the dual-primal gap (dense roots of weighted polynomials in
# [0.085, 0.72], their mirror images in [1.38, 11.2], the left support edge), plus a node exactly at every weighted root.
import os, numpy as np, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tpsets import load
setname, dualfile, out = sys.argv[1], sys.argv[2], sys.argv[3]
X = 11.2
P = load(setname); c = np.load(dualfile)[3:]
roots = []
for j, q in enumerate(P):
    if c[j] > 1e-6 and q != [1, 0]:
        r = np.roots(np.array(q, float)); rr = r[np.abs(r.imag) < 1e-9].real
        roots += [float(x) for x in rr if 0.05 < x < X]
roots = sorted(set(np.round(roots, 10)))
pts = set(np.round(np.arange(0.0, X + 1e-12, 0.004), 10))
pts |= set(np.round(np.arange(0.085, 0.72, 0.001), 10))
pts |= set(np.round(np.arange(0.085, 0.11, 0.00025), 10))           # left support edge
for r in roots:
    if r < 0.75:
        pts |= set(np.round(np.arange(r - 0.002, r + 0.002 + 1e-12, 0.00025), 10))
    else:
        pts |= set(np.round(np.arange(r - 0.003, r + 0.003 + 1e-12, 0.0005), 10))
    pts.add(round(r, 10))
for dip in [0.13015, 0.18492, 0.21129, 0.24373, 0.26225, 0.2648, 0.42884, 0.51597, 0.57921, 0.59999, 0.60841, 1.44755, 1.53353,
            2.0055, 2.1138, 3.13609, 3.41821, 3.70416, 7.16126]:
    pts |= set(np.round(np.arange(dip - 0.002, dip + 0.002 + 1e-12, 0.00025), 10))
e = np.array(sorted(x for x in pts if 0 <= x <= X)); keep = [0]
for i in range(1, len(e)):
    if e[i] - e[keep[-1]] >= 1e-4: keep.append(i)
if keep[-1] != len(e) - 1: keep[-1] = len(e) - 1
e = e[keep]
np.save(out, e); print(f"{len(roots)} weighted roots, {len(e)} nodes; min gap {np.diff(e).min():.2e}; X = {e[-1]}")
