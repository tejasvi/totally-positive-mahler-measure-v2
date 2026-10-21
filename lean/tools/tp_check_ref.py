"""Exact integer reference implementation of the Lean checker TPCore.Check (certificate a5), and the generator of
its leaves (the tiling of [x0, x_hi] into chord intervals and root windows). Mirrors the Lean code operation by operation
(floor = Python //, same rounding directions). Not part of any proof: the Lean checker re-verifies every leaf.

usage: python3 -I tp_check_ref.py CERT.json OUT_leaves.json [workers]
"""
import json, sys, math, os
from fractions import Fraction as Fr

P = 64           # scale of point quantities (logs, F)
QS = 64          # scale of the C_i
J = 7            # series terms after table reduction (z <= 1/33)
W = 66           # table field width
DEC = 10 ** 10   # node denominator

# ---------------------------------------------------------------- logarithm (mirror of AuxCore.LogK)
def atanhK(p, z2, n, j, pw, acc):
    for _ in range(n):
        acc += pw // (2 * j + 1)
        pw = (pw * z2) >> p
        j += 1
    return acc, pw

def logRatK(p, Jn, A, B):
    zl = ((A - B) * (1 << p)) // (A + B)
    acc, pw = atanhK(p, (zl * zl) >> p, Jn, 0, zl, 0)
    d = 8 * (2 * Jn + 1)
    tail = (9 * (pw + 6) + d - 1) // d
    return 2 * acc, 2 * (acc + 7 * Jn + tail)

def roundOut(g, r):
    return (r[0] >> g, (r[1] + (1 << g) - 1) >> g)

def mkTable(p, g, Jn, Wd):
    T = 0
    for i in range(16):
        lo, hi = roundOut(g, logRatK(p + g, Jn, 16 + i, 16))
        T |= (lo << (Wd * 2 * i)) | (hi << (Wd * (2 * i + 1)))
    return T

TAB = mkTable(P, 24, 48, W)
L2 = roundOut(24, logRatK(P + 24, 48, 2, 1))

def logK(a, b):
    """enclosure (lo, hi) of 2^P log(a/b), a, b > 0"""
    s = a.bit_length() - 1; t = b.bit_length() - 1
    A0 = a << t; B = b << s
    if B <= A0: A, e = A0, s - t
    else: A, e = A0 << 1, s - t - 1
    i = (16 * (A - B)) // B
    lo, hi = logRatK(P, J, 16 * A, (16 + i) * B)
    m = (1 << W) - 1
    lo += (TAB >> (W * 2 * i)) & m
    hi += (TAB >> (W * (2 * i + 1))) & m
    if e >= 0: return lo + e * L2[0], hi + e * L2[1]
    return lo + e * L2[1], hi + e * L2[0]

# ---------------------------------------------------------------- interval helpers (integers)
def fdiv(a, b):  # floor(a/b), b > 0
    return a // b
def cdiv(a, b):  # ceil(a/b), b > 0
    return -((-a) // b)
def encl1(g, H):  # enclosure of sum g_n v^n for v in [0, H] (one-sided)
    lo = g[0] if g else 0; hi = lo
    for n in range(1, len(g)):
        t = g[n] * H ** n
        if t < 0: lo += t
        else: hi += t
    return (lo, hi)

def deriv(g):
    return [n * g[n] for n in range(1, len(g))]

def imul(a, b):  # interval product, a=(lo,hi), b=(lo,hi)
    xs = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(xs), max(xs))

# ---------------------------------------------------------------- certificate
class Cert:
    def __init__(self, path):
        c = json.load(open(path))
        self.polys = c['polys']                      # descending coefficients
        self.cw = [Fr(x) for x in c['c']]
        for x in self.cw: assert x.denominator & (x.denominator - 1) == 0  # dyadic
        nodes = [Fr(x) for x in c['nodes']]
        assert all((x * DEC).denominator == 1 for x in nodes)
        self.n = [int(x * DEC) for x in nodes]
        G = [Fr(x) for x in c['G']]
        self.GS = max(x.denominator for x in G).bit_length() - 1
        assert all((x * (1 << self.GS)).denominator == 1 for x in G)
        self.g = [int(x * (1 << self.GS)) for x in G]
        self.m0 = Fr(c['m'])
        self.N = len(self.n) - 1
        N = self.N
        # slopes and slope jumps C_i (exact), fixed point at 2^QS
        sn = [(self.g[k + 1] - self.g[k]) * DEC for k in range(N)]
        sd = [(self.n[k + 1] - self.n[k]) << self.GS for k in range(N)]
        self.C = []   # (num, den, clo, chi)
        for i in range(N + 1):
            if 0 < i < N: num, den = sn[i] * sd[i - 1] - sn[i - 1] * sd[i], sd[i] * sd[i - 1]
            elif i == 0: num, den = sn[0], sd[0]
            else: num, den = -sn[N - 1], sd[N - 1]
            self.C.append((num, den, fdiv(num << QS, den), cdiv(num << QS, den)))
        # s exact = sum (n_{k+1}-n_k)(g_k+g_{k+1}) / (2 DEC 2^GS)
        self.s_num = sum((self.n[k + 1] - self.n[k]) * (self.g[k] + self.g[k + 1]) for k in range(N))
        self.s_den = 2 * DEC << self.GS
        # constants at scale 2^P
        self.m0hi = cdiv(self.m0.numerator << P, self.m0.denominator)
        self.cw_num = [x.numerator for x in self.cw]; self.cw_sh = [x.denominator.bit_length() - 1 for x in self.cw]
        self.deg = [len(q) - 1 for q in self.polys]
        # sum |C_i| upper bound at scale 2^QS
        self.sumabsC = sum(max(abs(c[2]), abs(c[3])) for c in self.C)

    def budget_ok(self):
        # sum c_j deg_j + 2 s < 1, exact
        return sum(self.cw[j] * self.deg[j] for j in range(len(self.polys))) + Fr(2 * self.s_num, self.s_den) < 1

# ---------------------------------------------------------------- per-point pieces
def poly_taylor(coeffs_desc, X, D):
    """beta_n (ascending): R(v) = D^d Q((X+v)/D) = sum beta_n v^n (exact integers)"""
    d = len(coeffs_desc) - 1
    a = list(reversed(coeffs_desc))   # ascending a_m
    b = [a[m] * D ** (d - m) for m in range(d + 1)]
    for i in range(d):
        for j in range(d - 1, i - 1, -1):
            b[j] += X * b[j + 1]
    return b

def Is_lo(cert, Ilo_num, Ilo_sh):
    """lower bound of 2^P I/s given I >= Ilo_num / 2^Ilo_sh"""
    # I/s >= Ilo * s_den / s_num (s > 0)
    return fdiv(Ilo_num * cert.s_den << P, cert.s_num << Ilo_sh)

class Ctx:
    def __init__(self, cert, Ilo_num, Ilo_sh):
        self.c = cert
        self.Islo = Is_lo(cert, Ilo_num, Ilo_sh)

    def node_pass(self, Xp, Xq, k):
        """one pass over the nodes for a leaf [Xp, Xq]/D (Xq may equal Xp for a point).
        Returns dict with U-sum intervals at p and q (scale 2^(P+QS+2), times D^2), the node part of M (scale 2^(P+QS)),
        the singular-node info, and whether a node lies strictly inside."""
        c = self.c
        D = DEC << k
        LD = logK(D, 1)
        Sp = [0, 0]; Sq = [0, 0]; M = 0; inside = False
        twoP34 = 3 << P
        for i in range(c.N + 1):
            num, den, clo, chi = c.C[i]
            if num == 0: continue
            ni = c.n[i] << k
            dp = ni - Xp; dq = ni - Xq
            if dp > 0 and dq < 0: inside = True; continue
            ap = abs(dp); aq = abs(dq)
            Lp = logK(ap, 1) if ap else None
            Lq = logK(aq, 1) if aq else None
            singular_pos = (num > 0) and (ap == 0 or aq == 0)
            # U terms: 4 Y 2^P = a^2 (2 (L - LD) - 3 2^P)
            if ap and not (singular_pos):
                Y = (ap * ap * (2 * (Lp[0] - LD[1]) - twoP34), ap * ap * (2 * (Lp[1] - LD[0]) - twoP34))
                t = imul((clo, chi), Y); Sp[0] += t[0]; Sp[1] += t[1]
            if aq and not (singular_pos):
                Y = (aq * aq * (2 * (Lq[0] - LD[1]) - twoP34), aq * aq * (2 * (Lq[1] - LD[0]) - twoP34))
                t = imul((clo, chi), Y); Sq[0] += t[0]; Sq[1] += t[1]
            # M node term: upper bound of -2 C_i log|x - e_i| on [p,q] (not for singular_pos)
            if Xq > Xp and not singular_pos:
                if ap and aq:
                    vlo = min(Lp[0], Lq[0]) - LD[1]; vhi = max(Lp[1], Lq[1]) - LD[0]
                elif ap:   # node at q, C < 0: log|x-e_i| <= log|p - e_i| = log h
                    vlo = None; vhi = Lp[1] - LD[0]
                else:
                    vlo = None; vhi = Lq[1] - LD[0]
                if num > 0:
                    M += -2 * (clo * vlo if vlo >= 0 else chi * vlo)
                else:
                    # -2 C v = 2 |C| v,  |C| in [-chi, -clo]
                    M += 2 * ((-clo) * vhi if vhi >= 0 else (-chi) * vhi)
        return dict(Sp=Sp, Sq=Sq, M=M, inside=inside, LD=LD, D=D)

    def U_hi(self, S, D):
        """upper bound of 2^P U from S (scale 2^(P+QS+2) D^2)"""
        return cdiv(S[1], (D * D) << (QS + 2))

    def logplus_lo(self, X, D):
        if X <= D: return 0
        return logK(X, D)[0]

    def chord_leaf(self, Xp, Xq, k, x0q, convmask):
        """lower bounds L(p), L(q) at scale 2^P; None if a structural check fails"""
        c = self.c
        if not Xp < Xq: return None
        D = DEC << k; H = Xq - Xp
        if Xp < D < Xq: return None               # 1 inside
        if H > D: return None                       # h <= 1
        r = self.node_pass(Xp, Xq, k)
        if r['inside']: return None
        LD = r['LD']
        Ap = self.logplus_lo(Xp, D) - c.m0hi + self.Islo - 2 * self.U_hi(r['Sp'], D)
        Aq = self.logplus_lo(Xq, D) - c.m0hi + self.Islo - 2 * self.U_hi(r['Sq'], D)
        Tx0 = 0; slope = 0      # slope term added to the far end (lower bound, scale 2^P)
        Mt = r['M']             # node part: scale 2^(P+QS), times h^2 later
        Mpoly = 0               # scale 2^P, already times h^2 (= H^2 / D^2 ... see below)
        for j, coef in enumerate(c.polys):
            beta = poly_taylor(coef, Xp, D)
            d = len(beta) - 1
            b1 = deriv(beta); b2 = deriv(b1)
            Wp = beta[0]; Wq = sum(beta[n] * H ** n for n in range(d + 1))
            R0 = encl1(beta, H); R1 = encl1(b1, H); R2 = encl1(b2, H)
            ex0 = R0[0] > 0 or R0[1] < 0
            mono = R1[0] > 0 or R1[1] < 0
            if not (ex0 or (mono and Wp * Wq > 0)): return None    # possible root in [p,q]
            cn, cs = c.cw_num[j], c.cw_sh[j]
            def mclog_lo(Wv):   # lower bound of -c_j log|Q_j| at scale 2^P
                Lw = logK(abs(Wv), 1)
                return fdiv(-cn * (Lw[1] - d * LD[0]), 1 << cs)
            sq = imul(R1, R1); sq = (max(sq[0], 0) if R1[0] * R1[1] >= 0 else 0, sq[1])
            RR = imul(R0, R2)
            if (convmask >> j) & 1:
                if sq[0] - RR[1] < 0: return None
                if x0q:
                    Tx0 += mclog_lo(Wq)
                    R1H = sum(b1[n] * H ** n for n in range(len(b1)))
                    slope += fdiv(cn * R1H * H << P, Wq << cs) if Wq > 0 else fdiv((-cn) * R1H * H << P, (-Wq) << cs)
                else:
                    Tx0 += mclog_lo(Wp)
                    R10 = b1[0] if b1 else 0
                    slope += fdiv(-cn * R10 * H << P, Wp << cs) if Wp > 0 else fdiv(cn * R10 * H << P, (-Wp) << cs)
            else:
                Ap += mclog_lo(Wp); Aq += mclog_lo(Wq)
                Nhi = sq[1] - RR[0]
                rlo = min(abs(R0[0]), abs(R0[1])) if ex0 else 0
                if mono: rlo = max(rlo, min(abs(Wp), abs(Wq)))
                if Nhi > 0:
                    Mpoly += cdiv(cn * H * H * Nhi << P, (rlo * rlo) << cs)
        # node M part times h^2/8:  M (scale 2^(P+QS)) * H^2 / D^2 -> scale 2^P
        Mn = cdiv(max(Mt, 0) * H * H, (D * D) << QS) if Mt > 0 else 0
        Mtot = Mn + Mpoly
        corr = cdiv(Mtot, 8)
        if x0q:
            Lp = Ap + Tx0 + slope - corr
            Lq = Aq + Tx0 - corr
        else:
            Lp = Ap + Tx0 - corr
            Lq = Aq + Tx0 + slope - corr
        return Lp, Lq

    def window_leaf(self, Xu, Xv, k):
        c = self.c
        D = DEC << k; H = Xv - Xu
        if not Xu < Xv: return None
        r = self.node_pass(Xu, Xu, k)
        LD = r['LD']
        F = self.logplus_lo(Xu, D) - c.m0hi + self.Islo
        for j, coef in enumerate(c.polys):
            beta = poly_taylor(coef, Xu, D)
            d = len(beta) - 1
            R0 = encl1(beta, H); B = max(abs(R0[0]), abs(R0[1]))
            Lb = logK(B, 1)
            F += fdiv(-c.cw_num[j] * (Lb[1] - d * LD[0]), 1 << c.cw_sh[j])
        # U(x) <= U(u) + h * 46 * sum|C_i|
        Uu = self.U_hi(r['Sp'], D)
        dU = cdiv(47 * c.sumabsC * H << P, D << QS)
        return F - 2 * (Uu + dU)

# ---------------------------------------------------------------- tiling generator
def pt_val(X, k):
    return Fr(X, DEC << k)

def common(a, b):
    """bring points a=(X,k), b=(X,k) to a common k"""
    k = max(a[1], b[1])
    return a[0] << (k - a[1]), b[0] << (k - b[1]), k

def check_interval(args):
    """bisect [a, b] (points (X, k)) until every chord leaf passes; returns (leaves, fails)"""
    ctx, a, b, maxk = args
    leaves = []; fails = []; stack = [(a, b)]
    while stack:
        a, b = stack.pop()
        Xp, Xq, k = common(a, b)
        best = None
        for x0q in (True, False):
            # convex mask: try all polynomials convex on [p,q]
            mask = 0
            for j in range(len(ctx.c.polys)):
                mask |= (1 << j)
            res = None
            # first try with the full mask; the checker returns None if some j is not convex: then drop such j
            res = ctx.chord_leaf(Xp, Xq, k, x0q, mask)
            if res is None:
                mask = convex_mask(ctx, Xp, Xq, k)
                if mask is None: break
                res = ctx.chord_leaf(Xp, Xq, k, x0q, mask)
            if res is not None:
                lb = min(res)
                if best is None or lb > best[0]: best = (lb, x0q, mask)
        if best is not None and best[0] > 0:
            leaves.append(dict(Xp=Xp, Xq=Xq, k=k, x0q=best[1], mask=best[2], lb=best[0]))
        elif k >= maxk:
            fails.append(dict(Xp=Xp, Xq=Xq, k=k, lb=None if best is None else best[0]))
        else:
            m = (Xp + Xq, k + 1)
            stack.append(((Xp << 1, k + 1), m)); stack.append((m, (Xq << 1, k + 1)))
    return leaves, fails

def convex_mask(ctx, Xp, Xq, k):
    c = ctx.c; D = DEC << k; H = Xq - Xp; mask = 0
    for j, coef in enumerate(c.polys):
        beta = poly_taylor(coef, Xp, D); d = len(beta) - 1
        b1 = deriv(beta); b2 = deriv(b1)
        Wq = sum(beta[n] * H ** n for n in range(d + 1))
        R0 = encl1(beta, H); R1 = encl1(b1, H); R2 = encl1(b2, H)
        ex0 = R0[0] > 0 or R0[1] < 0; mono = R1[0] > 0 or R1[1] < 0
        if not (ex0 or (mono and beta[0] * Wq > 0)): return None
        sq = imul(R1, R1); sq = (max(sq[0], 0) if R1[0] * R1[1] >= 0 else 0, sq[1])
        RR = imul(R0, R2)
        if sq[0] - RR[1] >= 0: mask |= 1 << j
    return mask

KW = 60

def right_tail_lb(ctx, Xt):
    """lower bound (scale 2^P) of kappa log x_t - m0 + I/s - sum c_j log A_j(x_t), x_t = Xt / DEC"""
    c = ctx.c
    lx = logK(Xt, DEC)
    S = max(c.cw_sh)
    lhs = sum(c.cw_num[j] * c.deg[j] * (1 << (S - c.cw_sh[j])) * c.s_den for j in range(len(c.polys))) + 2 * c.s_num * (1 << S)
    kNum = (1 << S) * c.s_den - lhs; kDen = (1 << S) * c.s_den
    klog = fdiv(kNum * lx[0], kDen) if kNum >= 0 else fdiv(kNum * lx[1], kDen)
    part = 0
    for j, coef in enumerate(c.polys):
        d = len(coef) - 1
        num = sum(abs(a) * DEC ** n * Xt ** (d - n) for n, a in enumerate(coef))   # coef descending: a_n x^(d-n)
        part += fdiv(-c.cw_num[j] * logK(num, Xt ** d)[1], 1 << c.cw_sh[j])
    return klog - c.m0hi + ctx.Islo + part

XHI = None

def make_breaks(cert, roots, XHI):
    """initial chord intervals and windows; windows: (Xu, Xv, k)"""
    x0 = (DEC, 30); xhi = (XHI * DEC, 0); one = (DEC, 0)
    wins = []
    for r in roots:
        if r['mult'] > 1:   # the double root x = 1 of Q_1: wider window at scale 10^-10
            assert r['X0'] < (DEC << KW) < r['X1']
            wins.append((DEC - 10, DEC + 10, 0))
        else:
            wins.append((r['X0'] - 1, r['X1'] + 1, KW))
    wins.sort(key=lambda w: Fr(w[0], DEC << w[2]))
    merged = []
    for w in wins:
        if merged and Fr(w[0], DEC << w[2]) <= Fr(merged[-1][1], DEC << merged[-1][2]):
            a, b, k = merged[-1]; kk = max(k, w[2])
            merged[-1] = (a << (kk - k), max(b << (kk - k), w[1] << (kk - w[2])), kk)
        else: merged.append(w)
    wins = merged
    bps = {(X, 0) for X in cert.n if Fr(1, 2**30) <= Fr(X, DEC) <= XHI} | {x0, xhi, one}
    wpts = []
    for u, v, k in wins:
        bps |= {(u, k), (v, k)}; wpts.append((Fr(u, DEC << k), Fr(v, DEC << k)))
    bps = sorted(bps, key=lambda t: pt_val(*t)); uniq = []
    for t in bps:
        if uniq and pt_val(*uniq[-1]) == pt_val(*t): continue
        uniq.append(t)
    ivs = [(uniq[i], uniq[i + 1]) for i in range(len(uniq) - 1)
           if not any(wu <= pt_val(*uniq[i]) and pt_val(*uniq[i + 1]) <= wv for wu, wv in wpts)]
    return ivs, wins

def main():
    import multiprocessing as mp, time
    cert = Cert(sys.argv[1]); out = sys.argv[2]; workers = int(sys.argv[3]) if len(sys.argv) > 3 else os.cpu_count()
    roots = json.load(open(sys.argv[4]))
    assert cert.budget_ok()
    Ilo_sh = 128; Ilo_num = int(Fr('2.8781e-11') * (1 << Ilo_sh))   # claimed lower bound of I (to be verified by I shards)
    ctx = Ctx(cert, Ilo_num, Ilo_sh)
    XHI = next(x for x in range(12, 200) if right_tail_lb(ctx, x * DEC) > (1 << P) // 100)
    print('x_hi', XHI, 'right tail lb', right_tail_lb(ctx, XHI * DEC) / 2**P, flush=True)
    ivs, wins = make_breaks(cert, roots, XHI)
    print('windows', len(wins), 'initial chord intervals', len(ivs), flush=True)
    t0 = time.time()
    with mp.Pool(workers) as pool:
        res = pool.map(check_interval, [(ctx, a, b, 70) for a, b in ivs], chunksize=1)
    leaves = [l for r in res for l in r[0]]; fails = [f for r in res for f in r[1]]
    print('chord leaves', len(leaves), 'fails', len(fails), 'min lb', min(l['lb'] for l in leaves) / 2**P, f'{time.time()-t0:.0f}s', flush=True)
    wl = []
    for u, v, k in wins:
        lb = ctx.window_leaf(u, v, k)
        wl.append(dict(Xu=u, Xv=v, k=k, lb=lb))
    print('windows min lb', min(w['lb'] for w in wl) / 2**P, 'bad', sum(w['lb'] <= 0 for w in wl), flush=True)
    json.dump(dict(chord=leaves, windows=wl, fails=fails, Ilo=[Ilo_num, Ilo_sh], xhi=XHI), open(out, 'w'))

if __name__ == '__main__':
    main()
