"""Diagnostics for the tiling generator: per initial interval, number of checks (capped) and time."""
import sys, json, time, os
sys.argv_saved = list(sys.argv)
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tp_check_ref.py')).read().replace("if __name__ == '__main__':\n    main()", ''))

def diag_interval(args):
    ctx, a, b, cap = args
    t0 = time.time(); checks = 0; leaves = 0; stack = [(a, b)]; deepest = 0; worst = None
    while stack and checks < cap:
        a, b = stack.pop()
        Xp, Xq, k = common(a, b)
        checks += 1; deepest = max(deepest, k)
        best = None
        for x0q in (True, False):
            mask = convex_mask(ctx, Xp, Xq, k)
            if mask is None: break
            res = ctx.chord_leaf(Xp, Xq, k, x0q, mask)
            if res is not None:
                lb = min(res)
                if best is None or lb > best: best = lb
        if best is not None and best > 0: leaves += 1
        else:
            worst = (float(Fr(Xp, DEC << k)), float(Fr(Xq, DEC << k)), k, best, mask)
            m = (Xp + Xq, k + 1)
            stack.append(((Xp << 1, k + 1), m)); stack.append((m, (Xq << 1, k + 1)))
    return (float(pt_val(*a)), checks, leaves, len(stack), deepest, time.time() - t0, worst)

def main2():
    import multiprocessing as mp
    cert = Cert(sys.argv_saved[1]); roots = json.load(open(sys.argv_saved[2])); cap = int(sys.argv_saved[3])
    ctx = Ctx(cert, int(Fr('2.8781e-11') * (1 << 128)), 128)
    XHI = next(x for x in range(12, 200) if right_tail_lb(ctx, x * DEC) > (1 << P) // 100)
    print("x_hi", XHI, flush=True)
    ivs, wins = make_breaks(cert, roots, XHI)
    with mp.Pool(86) as pool:
        res = pool.map(diag_interval, [(ctx, a, b, cap) for a, b in ivs], chunksize=1)
    res.sort(key=lambda r: -r[1])
    tot = sum(r[1] for r in res); totl = sum(r[2] for r in res)
    print('intervals', len(res), 'checks', tot, 'leaves', totl, 'capped', sum(1 for r in res if r[3] > 0))
    for r in res[:25]: print(r)

main2()
