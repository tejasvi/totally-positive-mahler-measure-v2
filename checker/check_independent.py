"""Independent checker for a tpmahler-cert-v1 certificate (lower bound for the smallest limit point lambda+ of
Omega(alpha) = M(alpha)^{1/deg alpha} over totally positive algebraic integers), for the paper "A lower bound for
the smallest limit point of the absolute Mahler measure of totally positive algebraic integers".

Written from an earlier formulation of Lemma 2.2 of the paper and the certificate format, without reading the first
checker (check_certificate.py); the two share no code.

Claim checked: with rho = G(x) dx (G continuous, piecewise linear on the nodes e_0 < ... < e_N, G_0 = G_N = 0),
s = rho(R), U(x) = int log|x - y| drho(y), I = int int log|x - y| drho drho,
  F(x) = log+ x - m - sum_j c_j log|Q_j(x)| - 2 U(x) + I/s >= 0 for all x in (0, inf)   (F = +inf at roots),
plus the data conditions and the strict budget sum_j c_j deg Q_j + 2 s < 1 (exact rationals). With nu = rho/s and
lambda = s this is the hypothesis of Lemma 2.2 of the paper, so log lambda+ >= m.

Precision: ball arithmetic at 128 bits; the energy I at 192 bits.
Machinery:
  * the polynomials are factored over Z; equal irreducible factors are merged (weights add). Real roots come from
    FLINT's isolating balls (real roots exactly real); the rational roots (degree-1 factors) are exact breakpoints, the
    irrational positive roots get dyadic windows [p, q] (q - p ~ 2^-100) on which F >= -w log(q - p) + (ball bound of
    the other terms);
  * U and U' by closed forms per grid piece (antiderivatives of (A + gamma t) log|t|), not by second differences;
    U'' = sum_i C_i log|x - e_i|, U''' = sum_i C_i/(x - e_i) with the exact slope jumps C_i;
  * I by closed forms per pair of grid pieces (fourth antiderivative of log|t|), cross-checked by
    sum_{i,j} C_i C_j K4(e_i - e_j); 192-bit balls;
  * positivity on each interval [a, b] between breakpoints: second-order Taylor bound at the midpoint,
        F(x) >= F(m) - |F'(m)| h - N h^2/2 - h sum_{end nodes with C_i < 0} 2|C_i| L (1 - log L) + (split roots),
    N from the regular part of F'': terms with a singular point within 3 interval widths by their end values
    (monotone there), the others by the mean-value form F''(m) + [-h, h] F'''([a, b]); a root at an interval end (or
    in an adjacent window) is split off and bounded by its value at the far end; bisection on failure;
  * left tail (0, x_lo] (x_lo <= left end of supp G): -w_x log x >= -w_x log x_lo, -w log|x - theta| >= -w log theta,
    U(x) <= U(0) (log(y - x) <= log y on the support); right tail [X, inf):
    F >= kappa log x - m + I/s - R/x with kappa = 1 - sum c_j deg Q_j - 2 s, from |x - theta| <= x (0 <= theta <= 2x),
    |x - zeta| <= x + |zeta| and U(x) <= s log x (x >= e_N).
The tail cut points x_lo and X are chosen by the checker; the certificate's x_lo, x_hi are not used. It tries
x_lo = 1/16, 1/32, ..., 1/8192 (not beyond the left end of supp G) and takes the first one whose bound is positive;
X starts at max(1, e_N, floor(max root/2) + 1) and doubles until the bound is positive.
Usage: check_independent.py CERT.json NPROC   (exit status 0 iff VERIFIED). Refuses to run under python -O.
Environment (negative tests only): TPA_M (override m), TPA_SCALEG (multiply G), TPA_DROP (0-based indices j with
c_j set to 0), TPA_DEPTH (max bisection depth, default 40)."""
import json, sys, os, time
from fractions import Fraction as Fr
from flint import arb, acb, ctx, fmpz_poly
if not __debug__:
    raise SystemExit("refusing to run with assertions disabled (python -O)")
ctx.prec = 128


def A(fr):
    return arb(fr.numerator) / arb(fr.denominator)


def _tlog(t, p):
    """t^p log|t| for an arb ball t (p >= 1), safe if t contains 0."""
    if not t.contains(0):
        return t ** p * abs(t).log()
    r = abs(t).upper()
    if r == 0:
        return arb(0)
    assert r < arb("0.3")
    b = r ** p * (1 / r).log()
    return arb(0).union(b).union(-b)


def K1(t):          # K1' = log|t|
    return _tlog(t, 1) - t


def L2(t):          # L2' = t log|t|
    return _tlog(t, 2) / 2 - t * t / 4


def K2(t):          # K2' = K1
    return _tlog(t, 2) / 2 - 3 * t * t / 4


def K3(t):          # K3' = K2
    return _tlog(t, 3) / 6 - 11 * t ** 3 / 36


def K4(t):          # K4' = K3
    return _tlog(t, 4) / 24 - 25 * t ** 4 / 288


def K234(t):
    """(K2, K3, K4)(t) for t != 0 with one logarithm."""
    lg = abs(t).log()
    t2 = t * t
    t3 = t2 * t
    return t2 * (lg / 2 - arb(3) / 4), t3 * (lg / 6 - arb(11) / 36), t3 * t * (lg / 24 - arb(25) / 288)


# ------------------------------------------------------------------ certificate
class Cert:
    def __init__(self, path, m_override=None, scaleG=None, drop=()):
        d = json.load(open(path))
        assert d.get("format") == "tpmahler-cert-v1", "format"
        self.polys = d["polys"]
        for q in self.polys:
            assert len(q) >= 1 and all(type(a) is int for a in q), "integer coefficients"
            assert q[0] != 0, "nonzero leading coefficient"
        assert len(set(tuple(q) for q in self.polys)) == len(self.polys), "distinct polynomials"
        assert [1, 0] in self.polys, "x must be one of the polynomials"
        self.c = [Fr(x) for x in d["c"]]
        for j in drop:
            self.c[j] = Fr(0)
        assert len(self.c) == len(self.polys) and all(x >= 0 for x in self.c), "c_j >= 0"
        self.jx = self.polys.index([1, 0])
        assert self.c[self.jx] > 0, "c for x must be > 0"
        self.e = [Fr(x) for x in d["nodes"]]
        self.G = [Fr(x) for x in d["G"]]
        if scaleG is not None:
            self.G = [g * scaleG for g in self.G]
        N = len(self.e) - 1
        self.N = N
        assert N >= 1 and len(self.G) == N + 1
        assert self.e[0] >= 0 and all(self.e[k] < self.e[k + 1] for k in range(N)), "nodes strictly increasing, e_0 >= 0"
        assert all(g >= 0 for g in self.G) and self.G[0] == 0 and self.G[N] == 0, "G >= 0, G_0 = G_N = 0"
        self.m = Fr(d["m"]) if m_override is None else Fr(m_override)
        e, G = self.e, self.G
        self.s = sum((e[k + 1] - e[k]) * (G[k] + G[k + 1]) / 2 for k in range(N))
        assert self.s > 0, "s > 0"
        self.degsum = sum(cj * (len(q) - 1) for cj, q in zip(self.c, self.polys))
        self.budget = self.degsum + 2 * self.s
        self.slope = [(G[k + 1] - G[k]) / (e[k + 1] - e[k]) for k in range(N)]
        C = [self.slope[0]] + [self.slope[k] - self.slope[k - 1] for k in range(1, N)] + [-self.slope[N - 1]]
        assert sum(C) == 0 and sum(Ci * ei for Ci, ei in zip(C, e)) == 0
        self.C = C
        self.active = [k for k in range(N) if G[k] != 0 or G[k + 1] != 0]
        # factor over Z, merge equal irreducible factors
        self.const_poly = Fr(0)          # sum_j c_j log|content_j| is added as arb later
        self.contents = []
        fac = {}
        for q, cj in zip(self.polys, self.c):
            if cj == 0:
                continue
            P = fmpz_poly(list(reversed(q)))
            cont, facs = P.factor()
            self.contents.append((int(cont), cj))
            for f, ex in facs:
                key = tuple(int(x) for x in f.coeffs())
                fac[key] = fac.get(key, Fr(0)) + cj * ex
        self.factors = fac               # key: low-first coefficients of a primitive irreducible factor -> weight


# ------------------------------------------------------------------ energy (192-bit, parallel)
_W = {}


def _setup_worker_arrays():
    ctx.prec = 192
    c = _W["cert"]
    _W["E"] = [A(x) for x in c.e]
    _W["Gv"] = [A(x) for x in c.G]
    _W["gam"] = [A(x) for x in c.slope]


def _Ib_chunk(ks):
    _setup_worker_arrays()
    c = _W["cert"]
    E, Gv, gam = _W["E"], _W["Gv"], _W["gam"]
    act = c.active
    tot = arb(0)
    for k in ks:
        xs = ((k, -1), (k + 1, 1))
        for l in act:
            if l < k:
                continue
            val = arb(0)
            for (ix, sx) in xs:
                gx = Gv[ix]
                for (iy, sy) in ((l, -1), (l + 1, 1)):
                    hy = Gv[iy]
                    if ix == iy:
                        continue                       # t = 0: K2 = K3 = K4 = 0
                    t = E[iy] - E[ix]
                    k2, k3, k4 = K234(t)
                    term = -hy * gx * k2 - hy * gam[k] * k3 + gam[l] * gx * k3 + gam[l] * gam[k] * k4
                    val += term if sx * sy > 0 else -term
            tot += val if l == k else 2 * val
    return tot.str(80, radius=True)


def _Ia_chunk(idx):
    _setup_worker_arrays()
    c = _W["cert"]
    E = _W["E"]
    nz = _W["nz"]
    Cs = [A(c.C[i]) for i in nz]
    tot = arb(0)
    for a in idx:
        i = nz[a]
        s_ = arb(0)
        for b in range(a + 1, len(nz)):
            s_ += Cs[b] * K234(E[nz[b]] - E[i])[2]
        tot += 2 * Cs[a] * s_
    return tot.str(80, radius=True)


def energies(c, nproc):
    import multiprocessing as mp
    _W["cert"] = c
    _W["nz"] = [i for i in range(c.N + 1) if c.C[i] != 0]
    act = c.active
    chunks = [act[i::nproc * 4] for i in range(nproc * 4)]
    nz = list(range(len(_W["nz"])))
    chunks2 = [nz[i::nproc * 4] for i in range(nproc * 4)]
    with mp.get_context("fork").Pool(nproc) as pool:
        rb = pool.map(_Ib_chunk, chunks)
        ra = pool.map(_Ia_chunk, chunks2)
    old = ctx.prec
    ctx.prec = 192
    Ib = sum((arb(x) for x in rb), arb(0))
    Ia = sum((arb(x) for x in ra), arb(0))
    ctx.prec = old
    return Ib, Ia


# ------------------------------------------------------------------ evaluation context
class Ctx:
    def __init__(self, c, I, window_bits=100):
        self.c = c
        self.I = I
        N = c.N
        self.E = [A(x) for x in c.e]
        self.Gv = [A(x) for x in c.G]
        self.gam = [A(x) for x in c.slope]
        self.Cnz = [(i, c.e[i], A(c.C[i]), c.C[i]) for i in range(N + 1) if c.C[i] != 0]
        const = -A(c.m) + I / A(c.s)
        for cont, cj in c.contents:
            if abs(cont) != 1:
                const -= A(cj) * arb(abs(cont)).log()
        self.roots = []          # dict(theta, w, rat, win)
        self.pairs = []          # (u, v, w)
        self.right_R = arb(0)    # sum over roots not in [0, 2x] of w |zeta| (for the right tail)
        self.factor_info = []
        for key, wq in c.factors.items():
            w = A(wq)
            f = fmpz_poly(list(key))
            lead = int(key[-1])
            if abs(lead) != 1:
                const -= w * arb(abs(lead)).log()
            if f.degree() == 1:
                r = Fr(-key[0], key[1])
                self.roots.append(dict(theta=A(r), w=w, rat=r, win=None, deg=1))
                self.factor_info.append((key, float(wq), "rational root %s" % r))
                continue
            nreal = 0
            for rt, mult in f.complex_roots():
                assert mult == 1
                if rt.imag == 0:
                    th = rt.real
                    nreal += 1
                    win = None
                    if th > 0:
                        sc = 2 ** window_bits
                        p = Fr(int((th.lower() * sc).floor().unique_fmpz()), sc)
                        q = Fr(int((th.upper() * sc).ceil().unique_fmpz()), sc)
                        if p == q:
                            q = p + Fr(1, sc)
                        while not (A(p) < th.lower()):
                            p -= Fr(1, sc)
                        while not (A(q) > th.upper()):
                            q += Fr(1, sc)
                        win = (p, q)
                    else:
                        assert th < 0, "root 0 of a non-linear factor"
                    self.roots.append(dict(theta=th, w=w, rat=None, win=win, deg=f.degree()))
                else:
                    assert rt.imag.lower() > 0 or rt.imag.upper() < 0
                    if rt.imag > 0:
                        self.pairs.append((rt.real, rt.imag, w))
            self.factor_info.append((key, float(wq), "%d real roots, %d complex pairs" % (nreal, (f.degree() - nreal) // 2)))
        self.const = const
        # windows must be pairwise disjoint and contain no node
        wins = sorted(r["win"] for r in self.roots if r["win"] is not None)
        for (p1, q1), (p2, q2) in zip(wins, wins[1:]):
            assert q1 < p2, "overlapping windows"
        import bisect
        for (p, q) in wins:
            i = bisect.bisect_left(c.e, p)
            assert i > c.N or c.e[i] > q, "node inside a root window"
        rats = [r["rat"] for r in self.roots if r["rat"] is not None and r["rat"] > 0]
        for r in rats:
            assert not any(p <= r <= q for p, q in wins)

    # --- U and U' at a point or on a ball x (arb)
    def U_and_dU(self, x, need_d=True):
        E, Gv, gam = self.E, self.Gv, self.gam
        U = arb(0)
        dU = arb(0)
        logs = {}
        tt = {}
        for k in self.c.active:
            for i in (k, k + 1):
                if i not in tt:
                    t = E[i] - x
                    tt[i] = t
                    if not t.contains(0):
                        logs[i] = abs(t).log()
                    elif t.is_zero():
                        logs[i] = arb(0)     # x = e_i: the two log|0| terms of U' have coefficients -G_i and +G_i
            a, b = tt[k], tt[k + 1]
            Ak = Gv[k] - gam[k] * a
            U += Ak * (K1(b) - K1(a)) + gam[k] * (L2(b) - L2(a))
            if need_d:
                dU += -Ak * (logs[k + 1] - logs[k]) - gam[k] * (b - a)
        return U, dU


def F_point(X, m):
    """F(m), F'(m) at a rational point m (not a node, not a root)."""
    x = A(m)
    F = X.const
    dF = arb(0)
    if m > 1:
        F += x.log()
        dF += 1 / x
    for r in X.roots:
        d = x - r["theta"]
        F -= r["w"] * abs(d).log()
        dF -= r["w"] / d
    for (u, v, w) in X.pairs:
        D = (x - u) ** 2 + v * v
        F -= w * D.log()
        dF -= w * 2 * (x - u) / D
    U, dU = X.U_and_dU(x)
    F -= 2 * U
    dF -= 2 * dU
    return F, dF


NEAR = 3


def _dist(a, b, y):
    """float distance from the point y (Fraction or float) to [a, b] (assumed outside)."""
    yf = float(y)
    return min(abs(yf - float(a)), abs(yf - float(b)))


def Fpp_lower(X, a, b, m, splits):
    """lower bound of the regular part of F'' on [a, b]; also the slope jumps at end nodes."""
    xm = A(m)
    T = A(a).union(A(b))
    h = (A(b) - A(a)) / 2
    thr = NEAR * float(b - a)
    v2 = arb(0)
    v3 = arb(0)
    vnear = arb(0)
    if a >= 1:
        v2 += -1 / (xm * xm)
        v3 += 2 / T ** 3
    for idx, r in enumerate(X.roots):
        if idx in splits:
            continue
        th, w = r["theta"], r["w"]
        if _dist(a, b, th.mid()) < thr:
            da, db = A(a) - th, A(b) - th
            vnear += (w / (da * da)).union(w / (db * db))
        else:
            dm = xm - th
            v2 += w / (dm * dm)
            dT = T - th
            v3 += -2 * w / dT ** 3
    for (u, v, w) in X.pairs:
        dm = xm - u
        Dm = dm * dm + v * v
        v2 += -w * 2 * (v * v - dm * dm) / (Dm * Dm)
        dT = T - u
        DT = dT * dT + v * v
        v3 += -w * 4 * dT * (dT * dT - 3 * v * v) / DT ** 3
    sing = []
    for (i, ei, Ci, Cfr) in X.Cnz:
        if ei == a or ei == b:
            sing.append(Cfr)
            continue
        if _dist(a, b, ei) < thr:
            la = abs(A(a) - X.E[i]).log()
            lb = abs(A(b) - X.E[i]).log()
            vnear += -2 * Ci * la.union(lb)
        else:
            v2 += -2 * Ci * abs(xm - X.E[i]).log()
            v3 += -2 * Ci / (T - X.E[i])
    m3 = arb(abs(v3).upper())
    return v2 - h * arb(0).union(m3).union(-m3) + vnear, sing, h


def interval_check(X, a, b):
    m = (a + b) / 2
    Fm, dFm = F_point(X, m)
    Ffull = Fm
    xm = A(m)
    low_root = arb(0)
    splits = set()
    for idx, r in enumerate(X.roots):
        side = None
        if r["rat"] is not None:
            if r["rat"] == b:
                side = "right"
            elif r["rat"] == a:
                side = "left"
        elif r["win"] is not None:
            if r["win"][0] == b:
                side = "right"
            elif r["win"][1] == a:
                side = "left"
        if side is None:
            continue
        splits.add(idx)
        th, w = r["theta"], r["w"]
        d = xm - th
        Fm -= -w * abs(d).log()
        dFm -= -w / d
        if side == "right":             # root at or just beyond b: farthest point a
            far = (A(r["win"][1]) if r["win"] else A(r["rat"])) - A(a)
        else:                           # root at or just before a: farthest point b
            far = A(b) - (A(r["win"][0]) if r["win"] else A(r["rat"]))
        low_root += -w * far.log()
    lowpp, sing, h = Fpp_lower(X, a, b, m, splits)
    if not (lowpp.is_finite() and Fm.is_finite() and dFm.is_finite()):
        return False, None, Ffull
    Nn = -lowpp.lower()
    Nn = arb(Nn) if Nn > 0 else arb(0)
    L = A(b - a)
    assert L < 1
    S = arb(0)
    for Cfr in sing:
        if Cfr < 0:
            S += 2 * A(-Cfr) * L * (1 - L.log())
    low = Fm - abs(dFm) * h - Nn * h * h / 2 - h * S + low_root
    return low.lower() > 0, low, Ffull


def window_check(X, idx):
    r = X.roots[idx]
    p, q = r["win"]
    T = A(p).union(A(q))
    val = X.const
    if p >= 1:
        val += T.log()
    else:
        assert q <= 1
    for j, r2 in enumerate(X.roots):
        if j == idx:
            continue
        val -= r2["w"] * abs(T - r2["theta"]).log()
    for (u, v, w) in X.pairs:
        val -= w * ((T - u) ** 2 + v * v).log()
    U, _ = X.U_and_dU(T, need_d=False)
    val -= 2 * U
    val += -r["w"] * A(q - p).log()
    return val.lower() > 0, val


def left_tail(X, xlo):
    """F >= ... on (0, xlo]; returns the lower bound."""
    c = X.c
    T = arb(0).union(A(xlo))
    val = X.const
    for r in X.roots:
        th, w = r["theta"], r["w"]
        if r["rat"] == 0:
            val -= w * A(xlo).log()                 # -w log x >= -w log xlo on (0, xlo]
        elif th > 0:
            assert th > A(xlo), "positive root inside the left tail"
            val -= w * th.log()                     # |x - th| <= th
        else:
            val -= w * (A(xlo) - th).log()          # |x - th| <= xlo - th
    for (u, v, w) in X.pairs:
        val -= w * arb(((T - u) ** 2 + v * v).upper()).log()
    # U(x) <= U(0) for 0 <= x <= xlo <= (left end of supp G): there 0 < y - x <= y, so log|x - y| <= log y
    assert xlo <= c.e[c.active[0]]
    U0, _ = X.U_and_dU(arb(0), need_d=False)
    val -= 2 * arb(U0.upper())
    return val


def right_tail(X, Xr):
    """F >= kappa log x + K0 - R/x on [Xr, inf); returns the lower bound at Xr (increasing in x)."""
    c = X.c
    assert Xr >= 1 and Xr >= c.e[-1]
    kappa = 1 - c.degsum - 2 * c.s
    assert kappa > 0
    R = arb(0)
    for r in X.roots:
        th, w = r["theta"], r["w"]
        if th >= 0:
            assert th <= 2 * A(Xr), "root beyond 2 Xr"
        else:
            R += w * abs(th)
    for (u, v, w) in X.pairs:
        R += 2 * w * (u * u + v * v).sqrt()
    return A(kappa) * A(Xr).log() + X.const - R / A(Xr), kappa


# ------------------------------------------------------------------ driver
_X = None


def _jobs(jobs):
    X = _X
    maxdep = int(os.environ.get("TPA_DEPTH", "40"))
    n = 0
    worst = None
    fmin = None
    deep = 0
    for (p, q) in jobs:
        stack = [(p, q, 0)]
        while stack:
            a, b, dep = stack.pop()
            ok, low, Fm = interval_check(X, a, b)
            n += 1
            if Fm is not None and Fm.is_finite() and (fmin is None or Fm.lower() < fmin[0]):
                fmin = (float(Fm.lower()), float((a + b) / 2))
            if ok:
                lv = float(low.lower())
                if worst is None or lv < worst[0]:
                    worst = (lv, float(a), float(b))
                deep = max(deep, dep)
                continue
            if Fm is not None and Fm.is_finite() and Fm.upper() < 0:
                return False, n, worst, fmin, deep, "F < 0 at x = %.15g: F = %s" % (float((a + b) / 2), Fm.str(10))
            if dep >= maxdep:
                return False, n, worst, fmin, deep, "FAIL on [%.15g, %.15g] depth %d: bound %s" % (float(a), float(b), dep, low)
            mid = (a + b) / 2
            stack += [(a, mid, dep + 1), (mid, b, dep + 1)]
    return True, n, worst, fmin, deep, ""


def _win(idx):
    ok, val = window_check(_X, idx)
    return ok, idx, float(val.lower())


def main():
    import multiprocessing as mp
    global _X
    path, nproc = sys.argv[1], int(sys.argv[2])
    t0 = time.time()
    drop = tuple(int(x) for x in os.environ.get("TPA_DROP", "").split(",") if x != "")
    sg = os.environ.get("TPA_SCALEG")
    c = Cert(path, m_override=os.environ.get("TPA_M"), scaleG=Fr(sg) if sg else None, drop=drop)
    print("cert %s: %d polys, %d nodes on [%s, %s]" % (os.path.basename(path), len(c.polys), c.N + 1, c.e[0], c.e[-1]), flush=True)
    print("m = %s = %.12f; drop = %s; scaleG = %s" % (c.m, float(c.m), drop, sg), flush=True)
    print("s = %.15f; sum c_j deg Q_j = %.15f; budget sum c deg + 2s = %.15f  strict < 1 (exact): %s"
          % (float(c.s), float(c.degsum), float(c.budget), c.budget < 1), flush=True)
    if not c.budget < 1:
        print("INDEPENDENT VERDICT: NOT VERIFIED (budget sum c_j deg Q_j + 2 s < 1 fails)")
        return False
    Ib, Ia = energies(c, nproc)
    print("I (piece pairs)   = %s\nI (slope jumps)   = %s   overlap: %s  (%.0fs)" % (Ib, Ia, Ib.overlaps(Ia), time.time() - t0), flush=True)
    assert Ib.overlaps(Ia), "the two evaluations of I disagree"
    I = Ib if Ib.rad() < Ia.rad() else Ia
    X = Ctx(c, I)
    print("I/s = %s; constant -m + I/s - sum log|lead/content| = %s" % ((X.I / A(c.s)).str(8), X.const.str(15)), flush=True)
    for key, wq, info in X.factor_info:
        print("  factor deg %d (weight %.6e): %s" % (len(key) - 1, wq, info))
    nwin = sum(1 for r in X.roots if r["win"] is not None)
    print("  %d real roots (%d windows), %d complex pairs" % (len(X.roots), nwin, len(X.pairs)), flush=True)
    # tails
    xlo = None
    for cand in [Fr(1, 2 ** k) for k in range(4, 14)]:
        if cand <= c.e[c.active[0]] and all(r["theta"] > A(cand) for r in X.roots if r["rat"] != 0 and r["theta"] > 0):
            lb = left_tail(X, cand)
            if lb.lower() > 0:
                xlo = cand
                break
    assert xlo is not None, "left tail failed"
    print("left tail (0, %s]: F >= %s" % (xlo, left_tail(X, xlo).str(8)), flush=True)
    maxroot = max(float(r["theta"].mid()) for r in X.roots)
    Xr = max(Fr(1), c.e[-1], Fr(int(maxroot / 2) + 1))
    while True:
        rb, kappa = right_tail(X, Xr)
        if rb.lower() > 0:
            break
        Xr *= 2
        assert Xr < 10 ** 6, "right tail failed"
    print("right tail [%s, inf): kappa = %.6f, F >= %s at x = %s and increasing" % (Xr, float(kappa), rb.str(8), Xr), flush=True)
    # windows
    _X = X
    widx = [i for i, r in enumerate(X.roots) if r["win"] is not None]
    with mp.get_context("fork").Pool(nproc) as pool:
        wres = pool.map(_win, widx)
    wbad = [r for r in wres if not r[0]]
    print("%d root windows (width <= 2^-99): %s; smallest window bound %.4e" % (len(wres), "all OK" if not wbad else "%d FAIL" % len(wbad), min(r[2] for r in wres)), flush=True)
    if wbad:
        print("INDEPENDENT VERDICT: NOT VERIFIED (window)")
        return False
    # breakpoints
    pts = {xlo, Xr, Fr(1)}
    pts |= {e for e in c.e if xlo < e < Xr}
    for r in X.roots:
        if r["rat"] is not None and xlo < r["rat"] < Xr:
            pts.add(r["rat"])
        if r["win"] is not None:
            pts |= {r["win"][0], r["win"][1]}
    x = c.e[-1]
    while x + Fr(1, 4) < Xr:
        x += Fr(1, 4)
        pts.add(x)
    pts = sorted(pts)
    wins = {(r["win"][0], r["win"][1]) for r in X.roots if r["win"] is not None}
    jobs = [(p, q) for p, q in zip(pts, pts[1:]) if (p, q) not in wins]
    assert all(not any(wp < p < wq or wp < q < wq for wp, wq in wins) for p, q in jobs)
    print("%d main-range intervals on [%s, %s] (%.0fs)" % (len(jobs), xlo, Xr, time.time() - t0), flush=True)
    KJ = nproc * 8
    parts = [jobs[i::KJ] for i in range(KJ)]
    with mp.get_context("fork").Pool(nproc) as pool:
        res = pool.map(_jobs, parts)
    ok = all(r[0] for r in res)
    n = sum(r[1] for r in res)
    for r in res:
        if not r[0]:
            print("  ", r[5])
    ws = [r[2] for r in res if r[2] is not None]
    fm = [r[3] for r in res if r[3] is not None]
    deep = max(r[4] for r in res)
    if ws:
        w = min(ws)
        print("smallest certified interval lower bound %.4e on [%.10f, %.10f]" % w)
    if fm:
        f = min(fm)
        print("smallest F(midpoint) seen %.6e at x = %.10f" % f)
    print("main range: %s  (%d interval checks, max depth %d)  t=%.0fs" % (ok, n, deep, time.time() - t0))
    print("INDEPENDENT VERDICT:", "VERIFIED" if ok else "NOT VERIFIED", "log lambda+ >=", c.m, float(c.m))
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)
