# int log|Q| dnu for the certificate's nu = rho/s, from the closed form U_rho(z) = Re sum_i C_i H(e_i - z),
# H(t) = t^2/2 Log t - 3t^2/4 (principal Log; real t: log|t|), at the roots of Q (FLINT complex_roots).
# Usage: python3 -I exact_screen.py CERT.json F29.json OUT.json NPROC LIST.json [LIST.json ...]
# (the lists are written by search/enum_tp.py and search/enum_tp_par.py; see the README)
import sys, json, numpy as np
from fractions import Fraction as Fr
from multiprocessing import Pool

def load_measure(cert):
    c = json.load(open(cert))
    e = [Fr(x) for x in c['nodes']]; G = [Fr(x) for x in c['G']]
    N = len(e) - 1
    g = [(G[k+1] - G[k])/(e[k+1] - e[k]) for k in range(N)]
    C = [g[0]] + [g[i] - g[i-1] for i in range(1, N)] + [-g[N-1]]
    s = sum((e[k+1] - e[k])*(G[k] + G[k+1])/2 for k in range(N))
    assert sum(C) == 0 and sum(Ci*ei for Ci, ei in zip(C, e)) == 0
    nz = [i for i in range(N + 1) if C[i] != 0]
    return np.array([float(e[i]) for i in nz]), np.array([float(C[i]) for i in nz]), float(s)

E = Cc = S = None
def U(z):
    t = E - z
    if isinstance(z, complex) or np.iscomplexobj(z):
        t = t.astype(complex)
        with np.errstate(divide='ignore', invalid='ignore'):
            h = t*t/2*np.log(t) - 0.75*t*t
        h[t == 0] = 0
        return float(np.real(np.dot(Cc, h)))
    with np.errstate(divide='ignore', invalid='ignore'):
        h = t*t/2*np.log(np.abs(t)) - 0.75*t*t
    h[t == 0] = 0
    return float(np.dot(Cc, h))

def val(q):
    import flint
    f = flint.fmpz_poly(q[::-1])
    tot = np.log(abs(q[0]))
    for r, mult in f.complex_roots():
        re, im = float(r.real.mid()), float(r.imag.mid())
        if r.imag == 0 or im == 0.0:
            tot += mult*U(re)/S
        else:
            tot += mult*U(complex(re, im))/S
    return float(tot)

def init(cert):
    global E, Cc, S
    E, Cc, S = load_measure(cert)

if __name__ == '__main__':
    cert, f29, out, nproc = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
    cands = []
    for fn in sys.argv[5:]:
        cands += json.load(open(fn))
    members = json.load(open(f29))
    mset = {tuple(q) for q in members}
    with Pool(nproc, initializer=init, initargs=(cert,)) as pool:
        mv = pool.map(val, members)
        cv = pool.map(val, cands, chunksize=500)
    init(cert)
    print('s =', S, ' nonzero C:', len(Cc))
    print('members (min %.3e):' % min(mv))
    for q, v in sorted(zip(members, mv), key=lambda t: t[1])[:8]:
        print('  %+.4e  deg %d  %s' % (v, len(q) - 1, q))
    outside = [(v, q) for q, v in zip(cands, cv) if tuple(q) not in mset]
    inside = [(v, q) for q, v in zip(cands, cv) if tuple(q) in mset]
    outside.sort(key=lambda t: t[0])
    print('candidates %d, outside the set %d, members among candidates %d' % (len(cands), len(outside), len(inside)))
    print('lowest outside:')
    for v, q in outside[:25]:
        print('  %+.4e  deg %d  %s' % (v, len(q) - 1, q))
    json.dump(dict(members=[(q, v) for q, v in zip(members, mv)], lowest_outside=[(q, v) for v, q in outside[:2000]]),
              open(out, 'w'))
