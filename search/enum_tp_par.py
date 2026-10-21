# Parallel driver for enum_tp.py (same pruning and the same DFS order): enumerate the prefixes c_{d-1}..c_{d-depth} serially,
# finish each subtree in a worker, concatenate in prefix order, keep the irreducible ones.  Usage: d R tfac out [nproc] [depth]
import os, numpy as np, sys, json, time
from math import comb
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from enum_tp import crit_interval, realroots_in
def walk(d, R, T, c, m_start, m_stop, sink):
    """the recursion of enum_tp.enumerate_tp from coefficient index m_start down; calls sink(c, m) after choosing c_m = stop level."""
    def rec(m):
        s = [0.0] + [comb(k, m)*c[k] for k in range(m+1, d+1)]
        if m == d-1:
            lo, hi = -T, 0.0
        else:
            lo, hi = crit_interval(np.array(s, dtype=float), R)
        if hi < lo - 1e-9: return
        for cm in range(int(np.ceil(lo - 1e-9)), int(np.floor(hi + 1e-9)) + 1):
            c[m] = cm
            r_low = [cm] + s[1:]
            if not realroots_in(np.array(r_low[::-1], dtype=float), R): continue
            if m == m_stop: sink(list(c), m)
            else: rec(m-1)
        c[m] = 0
    rec(m_start)
def finish(args):
    d, R, T, c, m = args
    if m == 0: return [c[::-1]]
    out = []
    walk(d, R, T, list(c), m - 1, 0, lambda cc, mm: out.append(cc[::-1]))
    return out
if __name__ == '__main__':
    import flint
    d, R, tfac, outf = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    nproc = int(sys.argv[5]) if len(sys.argv) > 5 else 32; depth = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    T = tfac*d; t0 = time.time()
    pre = []
    c = [0]*(d+1); c[d] = 1
    walk(d, R, T, c, d - 1, max(0, d - depth), lambda cc, mm: pre.append((d, R, T, cc, mm)))
    print(f"{len(pre)} prefixes ({time.time()-t0:.0f}s)", flush=True)
    with Pool(nproc) as pool:
        parts = pool.map(finish, pre, chunksize=1)
    ps = [p for part in parts for p in part]
    irr = []
    for p in ps:
        fac = flint.fmpz_poly(p[::-1]).factor()
        if len(fac[1]) == 1 and fac[1][0][1] == 1 and fac[1][0][0].degree() == d: irr.append(p)
    print(f"d={d}: {len(ps)} real-rooted in [0,{R}] with trace<={tfac}d, irreducible {len(irr)} ({time.time()-t0:.0f}s)", flush=True)
    json.dump(irr, open(outf, 'w'))
