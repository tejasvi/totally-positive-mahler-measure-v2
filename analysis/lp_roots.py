"""Numerical observation: Smyth-type LP without energy, with log|Q(x)| = log|lead| + sum log|x - zeta| over
certified FLINT roots (accurate for high degree; Horner in double precision is not).
Usage: lp_roots.py POLYS.json [WEIGHTS.json [OVERRIDE_INDEX:VALUE ...]]"""
import json, sys
import numpy as np
from scipy.optimize import linprog
from flint import fmpz_poly, ctx
ctx.prec = 200
polys = [list(map(int, q)) for q in json.load(open(sys.argv[1]))]
J = len(polys); deg = np.array([len(q) - 1 for q in polys], float)
RT = []
for q in polys:
    f = fmpz_poly(list(reversed(q)))
    rs = []
    for z, mlt in f.complex_roots():
        rs += [complex(float(z.real.mid()), float(z.imag.mid()))]*int(mlt)
    assert len(rs) == f.degree()
    RT.append((np.log(abs(q[0])), np.array(rs)))
def logabs(j, x):
    lead, rs = RT[j]
    v = np.full_like(x, lead)
    for z in rs:
        with np.errstate(divide='ignore'):
            v += np.log(np.abs(x - z))
    return v
realroots = sorted(z.real for _, rs in RT for z in rs if abs(z.imag) < 1e-12 and z.real > 0)
def grid(n=60000, X=2000.0):
    g = np.concatenate([np.geomspace(1e-4, X, n), np.linspace(0.01, 12, n)])
    for r in realroots:
        g = np.concatenate([g, r + np.geomspace(1e-7, 2e-2, 40), r - np.geomspace(1e-7, 2e-2, 40)])
    return np.unique(g[g > 0])
def mat(xs):
    A = np.stack([logabs(j, xs) for j in range(J)], axis=1)
    ok = np.all(np.isfinite(A), axis=1)
    return xs[ok], A[ok]
def solve(xs):
    xs, A = mat(xs)
    lp = np.log(np.maximum(xs, 1.0))
    Aub = np.vstack([np.hstack([np.ones((len(xs), 1)), A]), np.concatenate([[0.0], deg])[None, :]])
    res = linprog(np.concatenate([[-1.0], np.zeros(J)]), A_ub=Aub, b_ub=np.concatenate([lp, [1.0]]),
                  bounds=[(None, None)] + [(0, None)]*J, method='highs')
    return res.x[0], res.x[1:]
def Fvals(w, m, xs):
    xs, A = mat(xs)
    return xs, np.log(np.maximum(xs, 1.0)) - m - A @ w
if len(sys.argv) > 2:
    w = np.array(json.load(open(sys.argv[2])), float)
    for ov in sys.argv[3:]:
        i, v = ov.split(':'); w[int(i)] = float(v)
    xs, F = Fvals(w, 0.0, grid(300000, 5000.0))
    i = np.argmin(F); print("given weights: min of log+ x - sum w log|Q| = %.9f at x = %.6f, Omega %.7f" % (F[i], xs[i], np.exp(F[i])))
    sys.exit(0)
xs = grid()
for it in range(8):
    m, c = solve(xs)
    fx, F = Fvals(c, m, grid(300000, 5000.0))
    i = np.argmin(F)
    print("iter %d: LP m = %.10f (Omega %.7f), min F fine %.3e at %.6f" % (it, m, np.exp(m), F[i], fx[i]), flush=True)
    if F[i] > -1e-10: break
    loc = np.where((F[1:-1] < F[:-2]) & (F[1:-1] < F[2:]) & (F[1:-1] < 0))[0] + 1
    xs = np.unique(np.concatenate([xs, fx[loc]]))
print("value m + min(F,0) = %.10f; sum c deg = %.6f" % (m + min(F[i], 0.0), float(c @ deg)))
print("nonzero weights:", [(j, float('%.4g' % c[j])) for j in range(J) if c[j] > 1e-12])
