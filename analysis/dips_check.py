# The auxiliary function of the round before the certificate (a3) near the nineteen hard-coded points of tp_nodes5.py.
# Usage: python3 -I dips_check.py REPO_ROOT
# f(x) = log+ x - sum c_k log|Q_k(x)| - 2 lam U_nu(x) (constants dropped), nu from primalN_a3.npy (hat masses), c, lam from
# primalN_a3_dualN_F29.npy, log|Q| from FLINT roots.
import sys, json, numpy as np
from flint import fmpz_poly
R = sys.argv[1]
a = np.load(f'{R}/search/scratch/primalN_a3.npy'); ne = int(a[1]); e = a[2:2 + ne]; p = a[2 + ne:]; p = p / p.sum()
du = np.load(f'{R}/search/scratch/primalN_a3_dualN_F29.npy'); lam = du[1]; c = du[3:]
polys = json.load(open(f'{R}/search/data/F29.json'))
assert len(c) == len(polys)
# density values at nodes from hat masses: hat_i has integral (e_{i+1} - e_{i-1})/2 (half at the ends)
g = np.zeros(ne); g[1:-1] = p * 2 / (e[2:] - e[:-2])          # interior hats with unit mass, peak 2/(r - l)
sl = np.diff(g) / np.diff(e)
C = np.concatenate([[sl[0]], np.diff(sl), [-sl[-1]]])
def U(x):
    t = e[None, :] - x[:, None]
    with np.errstate(divide='ignore', invalid='ignore'):
        h = t * t / 2 * np.log(np.abs(t)) - 0.75 * t * t
    h[t == 0] = 0
    return h @ C
roots = []
for q, ck in zip(polys, c):
    if ck <= 0: continue
    f = fmpz_poly(q[::-1]); rs = [complex(float(r.real.mid()), float(r.imag.mid())) for r, m in f.complex_roots() for _ in range(m)]
    roots.append((ck, abs(q[0]), np.array(rs)))
def f(x):
    v = np.log(np.maximum(1, x)) - 2 * lam * U(x)
    for ck, lead, rs in roots:
        v -= ck * (np.log(lead) + np.log(np.abs(x[:, None] - rs[None, :])).sum(1))
    return v
dips = [0.13015, 0.18492, 0.21129, 0.24373, 0.26225, 0.2648, 0.42884, 0.51597, 0.57921, 0.59999, 0.60841, 1.44755, 1.53353,
        2.0055, 2.1138, 3.13609, 3.41821, 3.70416, 7.16126]
for d in dips:
    x = np.linspace(d - 0.002, d + 0.002, 4001)
    v = f(x); i = int(np.argmin(v))
    Fv = v - du[0] + lam * du[2]
    print('%.5f  argmin %.6f  interior %s  rise to edges %.2e %.2e  F(dip) %.2e  min F %.2e' % (d, x[i], 0 < i < len(x) - 1, v[0] - v[i], v[-1] - v[i], Fv[2000], Fv[i]))
