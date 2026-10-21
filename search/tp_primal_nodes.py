# Primal SOCP over hats on arbitrary nodes (npy), objective log+ x, polynomial set restricted to indices with dual weight > thr.
import os, numpy as np, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tp_primal_hat import solve
from tpsets import load, ROOT
if __name__ == '__main__':
    setname, nodefile, tag = sys.argv[1], sys.argv[2], sys.argv[3]
    keep = None
    if len(sys.argv) > 5:
        c = np.load(sys.argv[4])[3:]; thr = float(sys.argv[5]); keep = [j for j in range(len(c)) if c[j] > thr]
    P = load(setname); idx = keep if keep is not None else list(range(len(P)))
    polys = [P[j] for j in idx]
    e = np.load(nodefile); t0 = time.time()
    val, pv, du, st = solve(e, polys, energy=True)
    sup = e[1:-1][pv > 1e-7*pv.max()]
    print(f"{setname}[{len(polys)} polys] nodes={len(e)} energy primal {val:.7f} (Omega {np.exp(val):.7f}) [{st}] support [{sup.min():.3f}, {sup.max():.3f}] ({time.time()-t0:.0f}s)", flush=True)
    print("   duals:", [(idx[j], round(float(cc), 7)) for j, cc in enumerate(du[1]) if cc > 1e-8], " lambda_E:", du[2], flush=True)
    np.save(f'{ROOT}/scratch/primalN_{tag}.npy', np.concatenate([[val, len(e)], e, pv]))
    import json; json.dump(idx, open(f'{ROOT}/scratch/primalN_{tag}_idx.json', 'w'))
