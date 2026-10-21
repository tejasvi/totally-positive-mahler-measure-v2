# Enumerate monic integer polynomials of degree d with all roots real in [0, R] and trace <= T (derivative pruning).
import numpy as np, sys, json
from math import comb
def realroots_in(poly_high_first, R, tol=1e-7):
    r = np.roots(poly_high_first)
    if len(r) == 0: return True
    if np.max(np.abs(r.imag)) > 1e-5*max(1.0, np.max(np.abs(r))): return False
    rr = r.real
    return rr.min() >= -tol and rr.max() <= R + tol
def crit_interval(s_coeffs_low, R):
    # s(x) = sum_{i>=1} s_i x^i (s_coeffs_low[0] = 0); find interval of c such that s + c has all roots real in [0, R].
    deg = len(s_coeffs_low) - 1
    sp = np.polynomial.polynomial.polyder(s_coeffs_low)
    z = np.polynomial.polynomial.polyroots(sp) if deg >= 2 else np.array([])
    z = np.sort(z.real) if len(z) else z
    vals = np.polynomial.polynomial.polyval(z, s_coeffs_low) if len(z) else np.array([])
    lead = s_coeffs_low[-1]  # positive
    lo, hi = -np.inf, np.inf
    # alternation: at critical points z_1<...<z_{deg-1}, need (-1)^{deg-1-i} (s(z_i)+c) >= 0 for i=0..deg-2 (0-indexed),
    # i.e. sign pattern from the right: at the largest critical point value <= 0, next >= 0, ...
    for i in range(len(z)):
        k = len(z) - 1 - i     # 0 for the largest critical point
        if k % 2 == 0: hi = min(hi, -vals[i])        # s(z)+c <= 0
        else: lo = max(lo, -vals[i])                 # s(z)+c >= 0
    # roots in [0,R]: sign of (s+c)(0) = c must be (-1)^deg * lead-sign (or zero), and (s+c)(R) >= 0
    if deg % 2 == 0: lo = max(lo, 0.0)
    else: hi = min(hi, 0.0)
    sR = np.polynomial.polynomial.polyval(R, s_coeffs_low)
    lo = max(lo, -sR)
    return lo, hi
def enumerate_tp(d, R, T):
    out = []
    # coefficients c_k of x^k, c_d = 1. Choose c_{d-1}, c_{d-2}, ..., c_0; at step choosing c_m, the polynomial
    # r_m(x) = sum_{k=m}^d binom(k,m) c_k x^{k-m} must have all roots in [0,R].
    c = [0]*(d+1); c[d] = 1
    def rec(m):
        # choose c_m given c_{m+1..d}
        s = [0.0] + [comb(k, m)*c[k] for k in range(m+1, d+1)]   # low-first, without constant
        if m == d-1:
            lo, hi = -T, 0.0   # c_{d-1} = -trace, trace in [0, T]
        else:
            lo, hi = crit_interval(np.array(s, dtype=float), R)
        if hi < lo - 1e-9: return
        for cm in range(int(np.ceil(lo - 1e-9)), int(np.floor(hi + 1e-9)) + 1):
            c[m] = cm
            r_low = [cm] + s[1:]
            if not realroots_in(np.array(r_low[::-1], dtype=float), R): continue
            if m == 0: out.append(c[::-1].copy())     # high-first
            else: rec(m-1)
        c[m] = 0
    rec(d-1)
    return out
if __name__ == '__main__':
    import flint
    dmax = int(sys.argv[1]); R = float(sys.argv[2]); tfac = float(sys.argv[3])
    allp = []
    dmin = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    for d in range(dmin, dmax+1):
        ps = enumerate_tp(d, R, tfac*d)
        irr = []
        for p in ps:
            fp = flint.fmpz_poly(p[::-1])
            fac = fp.factor()
            if len(fac[1]) == 1 and fac[1][0][1] == 1 and fac[1][0][0].degree() == d: irr.append(p)
        print(f"d={d}: {len(ps)} real-rooted in [0,{R}] with trace<={tfac}d, irreducible {len(irr)}", flush=True)
        allp += irr
        json.dump(allp, open(sys.argv[4], 'w'))
