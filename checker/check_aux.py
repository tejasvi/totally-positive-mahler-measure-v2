"""Auxiliary exact checks for a tpmahler certificate (format tpmahler-cert-v1, see certificate/FORMAT.md).

Usage: check_aux.py CERT.json   (exit status 0 iff checks 1 and 2 pass)

1. Factorizations. check_independent.py builds F from the factorization over Z that FLINT returns for each Q_k with
   c_k > 0. Here every such factorization is multiplied back, content * prod f^e, and compared with Q_k exactly.
2. The constant K. G is piecewise linear, so max G is the largest node value. The program computes max G / s exactly and
   checks that K = 2 max G / s is at most 4.88, the value used in Remark 3.4 of the paper.
3. Information only: the zero runs of G inside the hull of its support, and the widths of the root windows that
   check_independent.py builds (FLINT root balls at 128 bits, rounded outwards to the grid 2^-100)."""
import json
import sys
from fractions import Fraction as Fr
from flint import arb, ctx, fmpz_poly

ctx.prec = 128


def main(path):
    d = json.load(open(path))
    polys = d["polys"]
    c = [Fr(x) for x in d["c"]]
    e = [Fr(x) for x in d["nodes"]]
    G = [Fr(x) for x in d["G"]]
    N = len(e) - 1
    ok = True

    # 1. factorizations multiply back
    bad = 0
    factors = {}
    for q, ck in zip(polys, c):
        if ck == 0:
            continue
        P = fmpz_poly(list(reversed(q)))
        cont, facs = P.factor()
        prod = fmpz_poly([int(cont)])
        for f, ex in facs:
            prod *= f ** ex
            factors[tuple(int(x) for x in f.coeffs())] = f
        if prod != P:
            bad += 1
            print("factorization does not multiply back:", q)
    print("1. factorizations of %d polynomials with positive weight: %s" % (sum(1 for x in c if x > 0),
                                                                          "all multiply back" if bad == 0 else "%d FAIL" % bad))
    ok = ok and bad == 0

    # 2. K = 2 max G / s
    s = sum((e[k + 1] - e[k]) * (G[k] + G[k + 1]) / 2 for k in range(N))
    r = max(G) / s
    kok = s > 0 and 2 * r <= Fr(488, 100)
    print("2. s = %.12f, max G / s = %.10f, K = 2 max G / s = %.10f <= 4.88: %s" % (float(s), float(r), float(2 * r),
                                                                                   "yes" if kok else "NO"))
    ok = ok and kok

    # 3. information: zero runs of G inside the hull of its support, and root window widths
    pos = [k for k in range(N + 1) if G[k] > 0]
    lo, hi = e[pos[0] - 1], e[pos[-1] + 1]
    runs, k = [], pos[0]
    while k < pos[-1]:
        if G[k] == 0 and G[k + 1] == 0:
            j = k
            while G[j + 1] == 0:
                j += 1
            runs.append((e[k], e[j], j - k))
            k = j
        k += 1
    print("3. G vanishes outside [%s, %s] = [%.5f, %.5f] and on %d node intervals inside it, in %d runs:"
          % (lo, hi, float(lo), float(hi), sum(n for _, _, n in runs), len(runs)))
    for a, b, n in runs:
        print("     [%.6f, %.6f]  (%d intervals)" % (float(a), float(b), n))
    sc = 2 ** 100
    widths = []
    for key, f in factors.items():
        if f.degree() == 1:
            continue
        for rt, _ in f.complex_roots():
            if rt.imag == 0 and rt.real > 0:
                th = rt.real
                p = Fr(int((th.lower() * sc).floor().unique_fmpz()), sc)
                q = Fr(int((th.upper() * sc).ceil().unique_fmpz()), sc)
                if p == q:
                    q = p + Fr(1, sc)
                while not (arb(p.numerator) / arb(p.denominator) < th.lower()):
                    p -= Fr(1, sc)
                while not (arb(q.numerator) / arb(q.denominator) > th.upper()):
                    q += Fr(1, sc)
                widths.append((q - p) * sc)
    print("   %d root windows of check_independent.py; widths in units of 2^-100: min %s, max %s"
          % (len(widths), min(widths), max(widths)))
    print("AUX CHECKS: %s" % ("PASSED" if ok else "FAILED"))
    return ok


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1]) else 1)
