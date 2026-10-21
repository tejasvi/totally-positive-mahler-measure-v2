import AuxCore.LogK
import TPCore.Data

/-!
# The checker for the certificate (core Lean only)

Every quantity is an integer; real numbers appear only in the soundness proof (`TPMahler.CheckSound`).
Scales: logarithms and values of `F` at `2^P`; slope jumps `C_i` at `2^QS`; a point is `x = X / D` with
`D = 10^10 · 2^k`.

* `mkRecs` computes the node records `(n_i, sign C_i, ⌊2^QS C_i⌋, ⌈2^QS C_i⌉)` from the nodes and G values.
* `chordOK` checks a chord leaf `[p, q]`: lower bounds `L(p), L(q) > 0` of the linear minorant
  `chord_A - M_A h^2/8 + T(x₀) + T'(x₀)(x - x₀)` of `F = A + T` on `[p, q]` (`T`: the convex polynomial terms selected
  by `mask`, with the tangent at `x₀ ∈ {p, q}`, plus the slope-jump terms of nodes at `p` or `q` with `C_i > 0`, which
  are `≥ 0`).
* `windowOK` checks a window `[u, v]` (no smoothness needed: `|Q_j| ≤ B_j` on the window, `U ≤ U(u) + h · 47 ∑|C_i|`).
* `leftTailOK` checks `(0, x₀]`, `rightTailOK` checks `[x_hi, ∞)`.
-/

namespace TPCore

open AuxCore

/-! ## Constants -/

def P : Nat := 64
def QS : Nat := 64
def JT : Nat := 7
def WT : Nat := 66
def DEC : Nat := 10000000000

/-- `mkTable 64 24 48 66` (equality checked in `TPCore.DataOK`). -/
def TAB : Nat := mkTable 64 24 48 66
/-- Enclosure of `2^64 log 2`, rounded from `2^88` (checked in `TPCore.DataOK`). -/
def L2 : Nat × Nat := roundOut 24 (logRatK 88 48 2 1)

/-- `2^P log (a / b)`, enclosed. -/
def logT (tab : Nat) (l2 : Nat × Nat) (a b : Nat) : Int × Int :=
  logK P JT tab WT (Int.ofNat l2.1) (Int.ofNat l2.2) a b

/-! ## Integer interval helpers -/

/-- `⌊a / b⌋` for `b > 0`. -/
def fdiv (a : Int) (b : Nat) : Int := Int.ediv a (Int.ofNat b)
/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a : Int) (b : Nat) : Int := Int.neg (Int.ediv (Int.neg a) (Int.ofNat b))

/-- Interval product. -/
def imul (a b : Int × Int) : Int × Int :=
  let p1 := a.1 * b.1
  let p2 := a.1 * b.2
  let p3 := a.2 * b.1
  let p4 := a.2 * b.2
  (min (min p1 p2) (min p3 p4), max (max p1 p2) (max p3 p4))

/-! ## Node records -/

structure NRec where
  n : Nat
  sg : Int
  clo : Int
  chi : Int
deriving Repr, DecidableEq

/-- Records from the nodes and G values at scale `2^q`: `pn / pd` is the slope of the previous piece. -/
def mkRecsAux (q gs : Nat) : Int → Nat → List Nat → List Nat → List NRec
  | pn, pd, n0 :: n1 :: ns, g0 :: g1 :: gv =>
    let sn : Int := ((g1 : Int) - (g0 : Int)) * (DEC : Int)
    let sd : Nat := (n1 - n0) * 2 ^ gs
    let num : Int := sn * (pd : Int) - pn * (sd : Int)
    let den : Nat := sd * pd
    ⟨n0, Int.sign num, fdiv (num * 2 ^ q) den, cdiv (num * 2 ^ q) den⟩ :: mkRecsAux q gs sn sd (n1 :: ns) (g1 :: gv)
  | pn, pd, [n0], [_] => [⟨n0, Int.sign (-pn), fdiv (-pn * 2 ^ q) pd, cdiv (-pn * 2 ^ q) pd⟩]
  | _, _, _, _ => []

def mkRecs (gs : Nat) (ns gv : List Nat) : List NRec := mkRecsAux QS gs 0 1 ns gv

/-- `∑ |C_i|` (upper bound, scale `2^QS`). -/
def sumAbsC (rs : List NRec) : Nat := rs.foldl (fun a r => a + max r.clo.natAbs r.chi.natAbs) 0

/-! ## The node pass of a chord leaf -/

/-- Accumulator: U-sums at `p` and `q` (scale `2^(P+QS+2)`, times `D^2`), the node part of `M` (scale `2^(P+QS)`),
and a flag for a node strictly inside `(p, q)`. -/
structure LAcc where
  spl : Int
  sph : Int
  sql : Int
  sqh : Int
  m : Int
  inside : Bool

/-- `4 · 2^P · Y = a² (2 (L - LD) - 3 · 2^P)` with `L = log a`, `LD = log D`: enclosure. -/
def yEncl (a : Nat) (L LD : Int × Int) : Int × Int :=
  let a2 : Int := (a * a : Nat)
  (a2 * (2 * (L.1 - LD.2) - 3 * 2 ^ P), a2 * (2 * (L.2 - LD.1) - 3 * 2 ^ P))

def leafStep (tab : Nat) (l2 : Nat × Nat) (k Xp Xq : Nat) (LD : Int × Int) (a : LAcc) (r : NRec) : LAcc :=
  if r.sg = 0 then a else
  let ni : Nat := r.n * 2 ^ k
  if Xp < ni ∧ ni < Xq then { a with inside := true } else
  let ap : Nat := if Xp ≤ ni then ni - Xp else Xp - ni
  let aq : Nat := if Xq ≤ ni then ni - Xq else Xq - ni
  let sing : Bool := decide (0 < r.sg) && (ap == 0 || aq == 0)
  if sing then a else
  let Lp := logT tab l2 ap 1
  let Lq := logT tab l2 aq 1
  let up := if ap = 0 then ((0 : Int), (0 : Int)) else imul (r.clo, r.chi) (yEncl ap Lp LD)
  let uq := if aq = 0 then ((0 : Int), (0 : Int)) else imul (r.clo, r.chi) (yEncl aq Lq LD)
  -- node part of M: upper bound of -2 C_i log|x - e_i| on [p, q]
  let vlo : Int := min Lp.1 Lq.1 - LD.2
  let vhi : Int := (if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1
  let mt : Int :=
    if 0 < r.sg then -2 * (if 0 ≤ vlo then r.clo * vlo else r.chi * vlo)
    else 2 * (if 0 ≤ vhi then (-r.clo) * vhi else (-r.chi) * vhi)
  ⟨a.spl + up.1, a.sph + up.2, a.sql + uq.1, a.sqh + uq.2, a.m + mt, a.inside⟩

def leafPass (tab : Nat) (l2 : Nat × Nat) (rs : List NRec) (k Xp Xq : Nat) (LD : Int × Int) : LAcc :=
  rs.foldl (leafStep tab l2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩

/-! ## Point pass (windows and tails): upper bound of the U-sum at one point -/

def pointStep (tab : Nat) (l2 : Nat × Nat) (k X : Nat) (LD : Int × Int) (a : Int × Int) (r : NRec) : Int × Int :=
  if r.sg = 0 then a else
  let ni : Nat := r.n * 2 ^ k
  let ad : Nat := if X ≤ ni then ni - X else X - ni
  if ad = 0 then a else
  let u := imul (r.clo, r.chi) (yEncl ad (logT tab l2 ad 1) LD)
  (a.1 + u.1, a.2 + u.2)

def pointPass (tab : Nat) (l2 : Nat × Nat) (rs : List NRec) (k X : Nat) (LD : Int × Int) : Int × Int :=
  rs.foldl (pointStep tab l2 k X LD) (0, 0)

/-- Upper bound of `2^P U` from the U-sum (scale `2^(P+QS+2)`, times `D^2`). -/
def uHi (S : Int × Int) (D : Nat) : Int := cdiv S.2 (D * D * 2 ^ (QS + 2))

/-! ## Polynomials -/

/-- `(v + X) r` for an ascending coefficient list `r`. -/
def mulVX (X : Int) : List Int → List Int
  | [] => []
  | r0 :: rs => X * r0 :: addHead r0 (mulVX X rs)
where
  addHead (c : Int) : List Int → List Int
    | [] => [c]
    | h :: t => (c + h) :: t

/-- Ascending coefficients of `R(v) = D^d Q((X + v)/D)` from the descending coefficients of `Q`. -/
def taylorR (X D : Nat) (desc : List Int) : List Int :=
  (desc.foldl (fun (st : List Int × Int) a =>
    match st with
    | (r, dp) => (match mulVX (X : Int) r with
                  | [] => [a * dp]
                  | h :: t => (h + a * dp) :: t, dp * (D : Int))) ([], 1)).1

/-- `∑ γ_n H^n` (ascending list). -/
def evalAsc (H : Int) (g : List Int) : Int := g.foldr (fun c acc => c + H * acc) 0

/-- `∑_{n ≥ 1} |γ_n| H^n`. -/
def tailAbs (H : Nat) : List Int → Nat
  | [] => 0
  | _ :: t => H * (t.foldr (fun c acc => c.natAbs + H * acc) 0)

/-- Derivative of an ascending coefficient list. -/
def derivAsc (g : List Int) : List Int :=
  (g.drop 1).zipIdx.map (fun (c, i) => c * ((i + 1 : Nat) : Int))

/-- Enclosure of a polynomial (ascending) on `[0, H]` (one-sided: negative terms lower the lower end, positive terms
raise the upper end). -/
def encl (H : Nat) (g : List Int) : Int × Int :=
  match g with
  | [] => (0, 0)
  | c0 :: t =>
    (t.zipIdx.foldl (fun (acc : Int × Int) (q : Int × Nat) =>
      let v : Int := q.1 * (H : Int) ^ (q.2 + 1)
      if v < 0 then (acc.1 + v, acc.2) else (acc.1, acc.2 + v)) (c0, c0))

/-- `-c log |W / D^d|` lower bound at scale `2^P`, with `c = cn / 2^cs`. -/
def mcLogLo (tab : Nat) (l2 : Nat × Nat) (cn cs d : Nat) (W : Int) (LD : Int × Int) : Int :=
  fdiv (-(cn : Int) * ((logT tab l2 W.natAbs 1).2 - (d : Int) * LD.1)) (2 ^ cs)

/-- Per-polynomial data of a chord leaf: `none` if the polynomial may vanish on `[p, q]` or is required convex but is
not; otherwise `(add to A(p), add to A(q), add to T(x₀), slope term, M part)`, all lower bounds at scale `2^P` except the
`M` part (upper bound, scale `2^P`, already multiplied by `h²`). -/
def polyLeaf (tab : Nat) (l2 : Nat × Nat) (Xp Xq D : Nat) (LD : Int × Int) (x0q conv : Bool)
    (desc : List Int) (cn cs : Nat) : Option (Int × Int × Int × Int × Int) :=
  let H : Nat := Xq - Xp
  let d : Nat := desc.length - 1
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let b2 := derivAsc b1
  let R0 := encl H b
  let R1 := encl H b1
  let R2 := encl H b2
  let W0 := b.headD 0
  let Wq := evalAsc (H : Int) b
  let ex0 : Bool := decide (0 < R0.1) || decide (R0.2 < 0)
  -- `R'` has no zero on `[0, H]`: `R` is strictly monotone there
  let mono : Bool := decide (0 < R1.1) || decide (R1.2 < 0)
  if ex0 || (mono && decide (0 < W0 * Wq)) then
    let sq := imul R1 R1
    let sqlo : Int := if 0 ≤ R1.1 * R1.2 then max sq.1 0 else 0
    let RR := imul R0 R2
    if conv then
      if 0 ≤ sqlo - RR.2 then
        if x0q then
          let R1H := evalAsc (H : Int) b1
          let sl : Int := if 0 < Wq then fdiv ((cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)
                          else fdiv (-(cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)
          some (0, 0, mcLogLo tab l2 cn cs d Wq LD, sl, 0)
        else
          let R10 := b1.headD 0
          let sl : Int := if 0 < W0 then fdiv (-(cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)
                          else fdiv ((cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)
          some (0, 0, mcLogLo tab l2 cn cs d W0 LD, sl, 0)
      else none
    else
      let Nhi : Int := sq.2 - RR.1
      let r1 : Nat := if ex0 then min R0.1.natAbs R0.2.natAbs else 0
      let rmin : Nat := if mono then max r1 (min W0.natAbs Wq.natAbs) else r1
      let mp : Int := if 0 < Nhi then cdiv ((cn : Int) * (H : Int) * (H : Int) * Nhi * 2 ^ P) (rmin * rmin * 2 ^ cs)
                      else 0
      some (mcLogLo tab l2 cn cs d W0 LD, mcLogLo tab l2 cn cs d Wq LD, 0, 0, mp)
  else none

/-! ## Leaf checks -/

/-- Global constants of a check: table, log 2, node records, `⌈2^P m₀⌉`, lower bound of `2^P I/s`. -/
structure Ctx where
  tab : Nat
  l2 : Nat × Nat
  rs : List NRec
  m0hi : Int
  isLo : Int
  sumC : Nat
deriving DecidableEq

def logPlusLo (c : Ctx) (X D : Nat) : Int :=
  if X ≤ D then 0 else (logT c.tab c.l2 X D).1

/-- Lower bounds `(L(p), L(q))` of a chord leaf, or `none`. -/
def chordLB (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Option (Int × Int) :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xq - Xp
  if Xp < Xq ∧ ¬ (Xp < D ∧ D < Xq) ∧ H ≤ D then
    let LD := logT c.tab c.l2 D 1
    let r := leafPass c.tab c.l2 c.rs k Xp Xq LD
    if r.inside then none else
    let base : Int := c.isLo - c.m0hi
    let polyRes := (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
      (fun (acc : Option (Int × Int × Int × Int × Int)) (x : (List Int × Nat × Nat) × Nat) =>
        match acc with
        | none => none
        | some (ap, aq, t0, sl, mp) =>
          match polyLeaf c.tab c.l2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2 with
          | none => none
          | some (ap', aq', t0', sl', mp') => some (ap + ap', aq + aq', t0 + t0', sl + sl', mp + mp'))
      (some (0, 0, 0, 0, 0))
    match polyRes with
    | none => none
    | some (pap, paq, t0, sl, mp) =>
      let Ap := logPlusLo c Xp D + base + pap - 2 * uHi (r.spl, r.sph) D
      let Aq := logPlusLo c Xq D + base + paq - 2 * uHi (r.sql, r.sqh) D
      let mn : Int := if 0 < r.m then cdiv (r.m * (H : Int) * (H : Int)) (D * D * 2 ^ QS) else 0
      let corr : Int := cdiv (mn + mp) 8
      if x0q then some (Ap + t0 + sl - corr, Aq + t0 - corr)
      else some (Ap + t0 - corr, Aq + t0 + sl - corr)
  else none

def chordOK (c : Ctx) (Xp Xq k : Nat) (x0q : Bool) (mask : Nat) : Bool :=
  match chordLB c Xp Xq k x0q mask with
  | some (lp, lq) => decide (0 < lp) && decide (0 < lq)
  | none => false

/-- Lower bound of `F` on the window `[Xu, Xv] / D` (scale `2^P`). -/
def windowLB (c : Ctx) (Xu Xv k : Nat) : Int :=
  let D : Nat := DEC * 2 ^ k
  let H : Nat := Xv - Xu
  let LD := logT c.tab c.l2 D 1
  let S := pointPass c.tab c.l2 c.rs k Xu LD
  let polyPart := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun (acc : Int) (x : List Int × Nat × Nat) =>
      let R0 := encl H (taylorR Xu D x.1)
      let B : Nat := max R0.1.natAbs R0.2.natAbs
      acc + fdiv (-(x.2.1 : Int) * ((logT c.tab c.l2 B 1).2 - ((x.1.length - 1 : Nat) : Int) * LD.1)) (2 ^ x.2.2))
    0
  let dU : Int := cdiv ((47 * c.sumC * H : Nat) * 2 ^ P) (D * 2 ^ QS)
  logPlusLo c Xu D - c.m0hi + c.isLo + polyPart - 2 * (uHi S D + dU)

def windowOK (c : Ctx) (Xu Xv k : Nat) : Bool := decide (Xu < Xv) && decide (0 < windowLB c Xu Xv k)

end TPCore

namespace TPCore

open AuxCore

/-! ## Global quantities, tails, budget -/

/-- `s · (2 · 10^10 · 2^GS) = ∑ (n_{k+1} - n_k)(g_k + g_{k+1})`. -/
def sNumAux : List Nat → List Nat → Nat
  | n0 :: n1 :: ns, g0 :: g1 :: gv => (n1 - n0) * (g0 + g1) + sNumAux (n1 :: ns) (g1 :: gv)
  | _, _ => 0

def sNum : Nat := sNumAux nodes gvals
def sDen : Nat := 2 * DEC * 2 ^ GS

/-- Context with the claimed lower bound `I ≥ iNum / 2^iSh` of the energy. -/
def mkCtx (iNum : Int) (iSh : Nat) : Ctx :=
  let rs := mkRecs GS nodes gvals
  { tab := TAB, l2 := L2, rs := rs, m0hi := cdiv ((m0num : Int) * 2 ^ P) m0den,
    isLo := fdiv (iNum * (sDen : Int) * 2 ^ P) (sNum * 2 ^ iSh), sumC := sumAbsC rs }

/-- The degree budget `∑ c_j deg Q_j + 2 s < 1`, exactly: with `c_j = cn_j / 2^cs_j`, over the common denominator
`2^S · sDen` where `S ≥ max cs_j`. -/
def budgetOK : Bool :=
  let S := cwSh.foldl max 0
  let lhs : Nat := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ (S - x.2.2) * sDen) 0 + 2 * sNum * 2 ^ S
  decide (lhs < 2 ^ S * sDen)

/-- Left tail `(0, x₀]` with `x₀ = X0 / D`: `F ≥ -m₀ - c₀ log x₀ - ∑_{j ≥ 1} c_j log B_j - 2 (U(0) + x₀ · 47 ∑|C_i|) + I/s`
(requires `Q_0 = x`, `x₀ ≤ 1`). Lower bound at scale `2^P`. -/
def leftTailLB (c : Ctx) (X0 k : Nat) : Int :=
  let D : Nat := DEC * 2 ^ k
  let LD := logT c.tab c.l2 D 1
  let S := pointPass c.tab c.l2 c.rs k 0 LD
  let polyPart := (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
    (fun (acc : Int) (x : (List Int × Nat × Nat) × Nat) =>
      if x.2 = 0 then
        -- -c_0 log x ≥ -c_0 log x₀
        acc + fdiv (-(x.1.2.1 : Int) * (logT c.tab c.l2 X0 D).2) (2 ^ x.1.2.2)
      else
        let R0 := encl X0 (taylorR 0 D x.1.1)
        let B : Nat := max R0.1.natAbs R0.2.natAbs
        acc + fdiv (-(x.1.2.1 : Int) * ((logT c.tab c.l2 B 1).2 - ((x.1.1.length - 1 : Nat) : Int) * LD.1))
          (2 ^ x.1.2.2))
    0
  let dU : Int := cdiv ((47 * c.sumC * X0 : Nat) * 2 ^ P) (D * 2 ^ QS)
  c.isLo - c.m0hi + polyPart - 2 * (uHi S D + dU)

/-- Right tail `[x_t, ∞)`, `x_t = Xt / 10^10 ≥ max(1, e_N)`: for `x ≥ x_t`, `|Q_j(x)| ≤ x^{d_j} A_j` with
`A_j = ∑_n |a_n| x_t^{-n}` (`a_n` the coefficient of `x^{d_j - n}`), and `U(x) ≤ s log x`, so
`F(x) ≥ κ log x - b ≥ κ log x_t - b` with `κ = 1 - ∑ c_j deg_j - 2 s > 0`, `b = m₀ - I/s + ∑ c_j log A_j`.
Lower bound of `2^P (κ log x_t - b)`. -/
def rightTailLB (c : Ctx) (Xt : Nat) : Int :=
  let lx := logT c.tab c.l2 Xt DEC
  let S := cwSh.foldl max 0
  let kDen : Nat := 2 ^ S * sDen
  let kNum : Int := (kDen : Int) - ((List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ (S - x.2.2) * sDen) 0 + 2 * sNum * 2 ^ S : Nat)
  let klog : Int := if 0 ≤ kNum then fdiv (kNum * lx.1) kDen else fdiv (kNum * lx.2) kDen
  let aPart := (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun (acc : Int) (x : List Int × Nat × Nat) =>
      let d : Nat := x.1.length - 1
      let num : Nat := x.1.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (d - q.2)) 0
      acc + fdiv (-(x.2.1 : Int) * (logT c.tab c.l2 num (Xt ^ d)).2) (2 ^ x.2.2))
    0
  klog - c.m0hi + c.isLo + aPart

/-! ## The energy `I(ρ)` (shards by blocks of rows)

`I = ∑_{i,k} C_i C_k L(e_i - e_k) = (1 / (12 · 10^40)) ∑_{i < k} C_i C_k V_ik` with
`V_ik = d⁴ (log d - log 10^10 - 25/12)`, `d = n_k - n_i` (the nodes are increasing). Scales: `C` at `2^QI`, logarithms at
`2^PI`, terms at `2^(2 QI + PI)`. -/

def PI : Nat := 100
def QI : Nat := 100
def JI : Nat := 10
def WI : Nat := 102
/-- `mkTable 100 24 48 102` (checked in `TPCore.DataOK`). -/
def TABI : Nat := mkTable 100 24 48 102
def L2I : Nat × Nat := roundOut 24 (logRatK 124 48 2 1)

def logI (tab : Nat) (l2 : Nat × Nat) (a b : Nat) : Int × Int :=
  logK PI JI tab WI (Int.ofNat l2.1) (Int.ofNat l2.2) a b

def recsI : List NRec := mkRecsAux QI GS 0 1 nodes gvals

/-- `∑_{k} C_i C_k V_ik` over the records `rest` following `ri` (enclosure at scale `2^(2 QI + PI)`). -/
def iRow (tab : Nat) (l2 : Nat × Nat) (lDec : Int × Int) (ri : NRec) (rest : List NRec) : Int × Int :=
  let c25lo : Int := fdiv (25 * 2 ^ PI) 12
  let c25hi : Int := cdiv (25 * 2 ^ PI) 12
  rest.foldl (fun (acc : Int × Int) (rk : NRec) =>
    if rk.sg = 0 then acc else
    let d : Nat := rk.n - ri.n
    let L := logI tab l2 d 1
    let d4 : Int := ((d * d) * (d * d) : Nat)
    let t := imul (imul (ri.clo, ri.chi) (rk.clo, rk.chi)) (d4 * (L.1 - lDec.2 - c25hi), d4 * (L.2 - lDec.1 - c25lo))
    (acc.1 + t.1, acc.2 + t.2)) (0, 0)

/-- The rows `rs` (with their tails): `∑` of `iRow` over the first `cnt` records of `rs`. -/
def iBlockAux (tab : Nat) (l2 : Nat × Nat) (lDec : Int × Int) : Nat → List NRec → Int × Int → Int × Int
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | cnt + 1, r :: rest, acc =>
    let t := if r.sg = 0 then ((0 : Int), (0 : Int)) else iRow tab l2 lDec r rest
    iBlockAux tab l2 lDec cnt rest (acc.1 + t.1, acc.2 + t.2)

/-- Enclosure of `∑_{i0 ≤ i < i0 + cnt} ∑_{k > i} C_i C_k V_ik` (scale `2^(2 QI + PI)`). -/
def iBlock (i0 cnt : Nat) : Int × Int :=
  let tab := TABI
  let l2 := L2I
  iBlockAux tab l2 (logI tab l2 DEC 1) cnt (recsI.drop i0) (0, 0)

/-! ## Leaves, coverage, the complete check -/

/-- A leaf: `kind = 0` chord `[X1, X2] / D` (with `x0q`, `mask`), `kind = 1` window. -/
structure Leaf where
  kind : Nat
  X1 : Nat
  X2 : Nat
  k : Nat
  x0q : Bool
  mask : Nat
deriving Repr, DecidableEq

def leafOK (c : Ctx) (l : Leaf) : Bool :=
  if l.kind = 0 then chordOK c l.X1 l.X2 l.k l.x0q l.mask else windowOK c l.X1 l.X2 l.k

/-- `a / (10^10 2^ka) = b / (10^10 2^kb)`. -/
def ptEq (a ka b kb : Nat) : Bool := a * 2 ^ kb == b * 2 ^ ka

/-- The leaves tile `[X0 / D0, XT / DT]` in order (consecutive end points equal) and each passes. -/
def leavesOK (c : Ctx) : Nat → Nat → List Leaf → Nat → Nat → Bool
  | X, kx, [], XT, kT => ptEq X kx XT kT
  | X, kx, l :: ls, XT, kT => ptEq X kx l.X1 l.k && leafOK c l && leavesOK c l.X2 l.k ls XT kT

/-- Sanity of the data: `Q_0 = x`, positive weights, increasing nodes, `G_0 = G_N = 0`, `s > 0`, same lengths. -/
def dataOK : Bool :=
  polys.headD [] == [1, 0] && polys.length == cwNum.length && polys.length == cwSh.length &&
  cwNum.all (fun c => decide (0 < c)) && polys.all (fun q => decide (2 ≤ q.length) && decide (q.headD 0 ≠ 0)) &&
  nodes.length == gvals.length && gvals.headD 1 == 0 && gvals.getLast? == some 0 &&
  (List.zip nodes (nodes.drop 1)).all (fun x => decide (x.1 < x.2)) && decide (0 < sNum)

end TPCore
