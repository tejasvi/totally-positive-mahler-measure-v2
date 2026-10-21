# Parallel version of tp_screen.py: U_nu tabulated with the multiprocessing Unu of tp_dual_fixedN_par.
import os, numpy as np, sys, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tp_dual_fixedN_par import Unu
from tpc import _hat_quad_nodes
if __name__ == '__main__':
    prim, out = sys.argv[1], sys.argv[2]; cfiles = sys.argv[3:]
    a = np.load(prim); ne = int(a[1]); e = a[2:2 + ne]; p = a[2 + ne:]; p = p/p.sum()
    t0 = time.time(); grid = np.arange(0.0, 40.0, 1e-4); U = Unu(e, p, grid, nproc=48)
    print(f"U tabulated on {len(grid)} points ({time.time()-t0:.0f}s)", flush=True)
    Xq, Wq = _hat_quad_nodes(e); wflat = (Wq*p[:, None]).ravel(); xflat = Xq.ravel()
    cands = []
    for f in cfiles: cands += json.load(open(f))
    res = []
    for q in cands:
        r = np.roots(np.array(q, float)); val = np.log(abs(q[0]))
        rr = r[np.abs(r.imag) < 1e-9].real; rc = r[np.abs(r.imag) >= 1e-9]
        val += np.interp(rr, grid, U).sum() if len(rr) else 0.0
        for z in rc: val += wflat @ np.log(np.abs(xflat - z))
        res.append((float(val), len(q) - 1, q))
    res.sort(key=lambda t: t[0]); json.dump(res[:2000], open(out, 'w'))
    print(f"screened {len(res)} ({time.time()-t0:.0f}s); lowest:")
    for v, d, q in res[:20]: print(f"  {v:+.6f}  deg {d}  per-deg {v/d:+.5f}  {q}")
