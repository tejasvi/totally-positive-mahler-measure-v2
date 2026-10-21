# Adaptive hat nodes: base spacing on [0, X], fine spacing within +-win of given centres (roots of weighted polynomials, edges, dips).
import os, numpy as np, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tpsets import load, ROOT
def make_nodes(X, base, fine, win, centres):
    pts = set(np.round(np.arange(0.0, X + 1e-12, base), 10))
    for r in centres:
        for x in np.arange(r - win, r + win + 1e-12, fine):
            if 0 < x < X: pts.add(round(float(x), 10))
    e = np.array(sorted(pts)); keep = [0]
    for i in range(1, len(e)):
        if e[i] - e[keep[-1]] >= 0.5*fine: keep.append(i)
    if keep[-1] != len(e) - 1: keep[-1] = len(e) - 1
    return e[keep]
if __name__ == '__main__':
    setname, dualfile, thr, X, base, fine, win, out = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6]), float(sys.argv[7]), sys.argv[8]
    extra = [float(v) for v in sys.argv[9:]]
    P = load(setname); c = np.load(dualfile)[3:]
    cent = []
    for j, p in enumerate(P):
        if c[j] > thr:
            r = np.roots(np.array(p, float)); rr = r[np.abs(r.imag) < 1e-9].real; cent += list(rr[(rr > 0) & (rr < X)])
    cent = sorted(set(np.round(cent, 8))) + extra
    e = make_nodes(X, base, fine, win, cent)
    np.save(out, e); print(f"{len(cent)} centres, {len(e)} nodes, {len(e) - 2} hats; min gap {np.diff(e).min():.2e}")
