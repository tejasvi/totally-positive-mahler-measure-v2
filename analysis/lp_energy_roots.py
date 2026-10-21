"""Fixed-reference dual LP (floating point) with the certificate's own reference measure nu = rho/s and the 30-polynomial
search set F29, once with log|Q| by float64 Horner (np.polyval, as in repo/search/tp_dual_fixedN_par.py line 41) and once
with root products (accurate).
Usage: lp_energy_roots.py CERT.json F29.json MODE I_RHO  (MODE = horner | roots | roots_cert21; I_RHO = I(rho) of the
certificate as printed by the checkers; the default is that of an earlier certificate)"""
import json, sys, time
import numpy as np
from fractions import Fraction as Fr
from flint import fmpz_poly, ctx
from scipy.optimize import linprog

cert = json.load(open(sys.argv[1])); polys30 = json.load(open(sys.argv[2])); mode = sys.argv[3]
polys = cert['polys'] if mode == 'roots_cert21' else polys30
e = np.array([float(Fr(x)) for x in cert['nodes']]); Gf = [Fr(x) for x in cert['G']]; ef = [Fr(x) for x in cert['nodes']]
N = len(e) - 1
s = float(sum((ef[k + 1] - ef[k]) * (Gf[k] + Gf[k + 1]) / 2 for k in range(N)))
slope = [(Gf[k + 1] - Gf[k]) / (ef[k + 1] - ef[k]) for k in range(N)]
C = np.array([float(slope[0])] + [float(slope[k] - slope[k - 1]) for k in range(1, N)] + [float(-slope[N - 1])])
nz = np.nonzero(C)[0]; Cn = C[nz]; en = e[nz]
I_rho = float(sys.argv[4]) if len(sys.argv) > 4 else 1.5298247573547548e-10   # energy of rho (checker logs)
E = I_rho / s**2                          # I(nu)

def H(t):
    o = np.zeros_like(t); m = t != 0
    o[m] = t[m]**2 / 2 * np.log(np.abs(t[m])) - 0.75 * t[m]**2
    return o

def Unu(x, chunk=1500):
    out = np.empty(len(x))
    for i in range(0, len(x), chunk):
        xx = x[i:i + chunk][:, None]
        out[i:i + chunk] = (H(en[None, :] - xx) @ Cn) / s
    return out

ctx.prec = 120
def roots_of(q):
    P = fmpz_poly(list(reversed(q)))
    r = []
    for z, mu in P.complex_roots():
        r += [complex(float(z.real.mid()), float(z.imag.mid()))] * int(mu)
    return abs(int(P.coeffs()[-1])), np.array(r)

def logabs_roots(q, x):
    lead, r = roots_of(q)
    v = np.full(len(x), np.log(lead))
    for z in r:
        v += np.log(np.abs(x - z.real)) if z.imag == 0 else 0.5 * np.log((x - z.real)**2 + z.imag**2)
    return v

def logabs_horner(q, x):
    with np.errstate(divide='ignore'):
        return np.log(np.abs(np.polyval(np.array(q, float), x)))

t0 = time.time()
rr = sorted(set(round(z.real, 15) for q in polys for z in roots_of(q)[1] if z.imag == 0 and z.real > 0))
Xs = e[-1]
x = np.unique(np.concatenate([np.geomspace(1e-7, 0.02, 3000), np.arange(0.02, Xs + 0.5, 0.0005), e[1:-1],
                              0.5 * (e[1:] + e[:-1]), np.geomspace(Xs + 0.5, 80.0, 3000)]))
near = [np.concatenate([r + np.geomspace(1e-7, 0.02, 200), r - np.geomspace(1e-7, 0.02, 200)]) for r in rr if r < Xs + 0.5]
sub = np.linspace(0, 1, 9)[1:-1]
nodal = (e[:-1, None] + (e[1:] - e[:-1])[:, None] * sub[None, :]).ravel()
x = np.unique(np.concatenate([x] + near + [nodal])); x = x[x > 0]
x = x[np.min(np.abs(x[:, None] - np.array(rr)[None, :]), axis=1) > 1e-9]
U = Unu(x)
logabs = logabs_horner if mode == 'horner' else logabs_roots
L = np.array([logabs(q, x) for q in polys]).T
f = np.log(np.maximum(1.0, x)); ok = np.all(np.isfinite(L), axis=1); x, U, L, f = x[ok], U[ok], L[ok], f[ok]
print(f"mode {mode}: {len(polys)} polys, {len(x)} points, I(nu) = {E:.3e}, setup {time.time() - t0:.0f}s", flush=True)
degs = np.array([len(q) - 1 for q in polys], float); J = len(polys)
sel = np.arange(0, len(x), 20)
rows_extra = [np.concatenate([[0.0], degs, [2.0]])]; rhs_extra = [1.0 - 1e-6]
for it in range(60):
    A = np.hstack([np.ones((len(sel), 1)), L[sel], (2 * U[sel] - E)[:, None]])
    A = np.vstack([A] + [r[None, :] for r in rows_extra])
    res = linprog(np.concatenate([[-1.0], np.zeros(J + 1)]), A_ub=A, b_ub=np.concatenate([f[sel], rhs_extra]),
                  bounds=[(None, None)] + [(0, None)] * (J + 1), method='highs',
                  options={'primal_feasibility_tolerance': 1e-10, 'dual_feasibility_tolerance': 1e-10})
    m, c, lam = res.x[0], res.x[1:J + 1], res.x[J + 1]
    print(f"  it {it}: m = {m:.8f} rows {len(sel)} t = {time.time() - t0:.0f}s", flush=True)
    F = f - m - L @ c - lam * (2 * U - E); Fmin = F.min()
    if Fmin > -1e-10:
        break
    viol = np.nonzero(F < -1e-10)[0]
    lm = [i for i in viol if (i == 0 or F[i] <= F[i - 1]) and (i == len(F) - 1 or F[i] <= F[i + 1])]
    sel = np.unique(np.concatenate([sel, lm]))
print(f"mode {mode}: it {it} m = {m:.8f} (Omega {np.exp(m):.7f}) lambda = {lam:.5f} (s = {s:.5f}) min F = {Fmin:.2e}; "
      f"sum c deg + 2 lam = {degs @ c + 2 * lam:.4f}; {time.time() - t0:.0f}s")
print("positive weights (index:deg:weight):", ", ".join("%d:%d:%.2e" % (j, degs[j], c[j]) for j in range(J) if c[j] > 1e-12))
print("number with weight > 1e-12:", int(np.sum(c > 1e-12)))
