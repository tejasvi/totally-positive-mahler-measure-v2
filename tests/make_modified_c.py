"""negative-test certificates for the tpmahler audit (modified copies of the frozen certificate)."""
import json, sys, os
from fractions import Fraction as Fr
src, out = sys.argv[1], sys.argv[2]
d0 = json.load(open(src))
def save(name, d, note):
    d = dict(d); d["audit_note"] = note
    json.dump(d, open(os.path.join(out, name + ".json"), "w"))
    print(name, ":", note)
m = Fr(d0["m"])
for tag, dm in [("m_up_1e-5", Fr(1, 10**5)), ("m_up_4e-6", Fr(4, 10**6)), ("m_up_3p1e-6", Fr(31, 10**7)), ("m_up_2e-6", Fr(2, 10**6))]:
    d = dict(d0); d["m"] = str(m + dm); save("neg_" + tag, d, f"m raised by {dm}")
for j in range(len(d0["c"])):
    d = dict(d0); c = list(d0["c"]); c[j] = "0"; d["c"] = c; save(f"neg_drop_{j:02d}", d, f"c_{j} set to 0 (Q = {d0['polys'][j][:6]}...)")
for tag, s in [("G_x1.01", Fr(101, 100)), ("G_x0.99", Fr(99, 100)), ("G_x1.0001", Fr(10001, 10000)), ("G_x0.9999", Fr(9999, 10000))]:
    d = dict(d0); d["G"] = [str(Fr(g) * s) for g in d0["G"]]; save("neg_" + tag, d, f"G scaled by {s}")
jx = d0["polys"].index([1, 0])
d = dict(d0); c = list(d0["c"]); c[jx] = str(Fr(c[jx]) * Fr(1001, 1000)); d["c"] = c; save("neg_cx_x1.001", d, "c_x scaled by 1.001")
# budget boundary (exact: s is rational): shift c_x so that sum c deg + 2 s = 1 exactly, and 1 - 1e-30
e = [Fr(x) for x in d0["nodes"]]; G = [Fr(x) for x in d0["G"]]
s = sum((e[k + 1] - e[k]) * (G[k] + G[k + 1]) / 2 for k in range(len(e) - 1))
degsum = sum(Fr(cc) * (len(q) - 1) for cc, q in zip(d0["c"], d0["polys"]))
for tag, target in [("budget_eq_1", Fr(1)), ("budget_1_minus_1e-30", 1 - Fr(1, 10**30))]:
    c = list(d0["c"]); c[jx] = str(Fr(c[jx]) + (target - degsum - 2 * s)); d = dict(d0); d["c"] = c
    save("neg_" + tag, d, f"c_x shifted so that sum c deg + 2s = {target}")
d = dict(d0); G2 = list(d0["G"]); G2[500] = "-1/1000000"; d["G"] = G2; save("neg_negative_G", d, "G_500 = -1e-6")
d = dict(d0); G2 = list(d0["G"]); G2[-1] = "1/1000"; d["G"] = G2; save("neg_GN_nonzero", d, "G_N = 1/1000")
d = dict(d0); n2 = list(d0["nodes"]); n2[1000], n2[1001] = n2[1001], n2[1000]; d["nodes"] = n2; save("neg_nodes_swapped", d, "nodes 1000 and 1001 swapped")
j2 = d0["polys"].index([1, -3, 1]); d = dict(d0); p2 = [list(q) for q in d0["polys"]]; p2[j2] = [1, -3, 2]; d["polys"] = p2
save("neg_poly_x2-3x+2", d, "x^2 - 3x + 1 replaced by x^2 - 3x + 2")
