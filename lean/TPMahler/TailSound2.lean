import TPMahler.CheckSound9

/-!
# Soundness of the checker: the degree budget and the two tails

* `budget_sound`: `budgetOK` gives `∑ cⱼ deg Qⱼ + 2 s < 1`;
* `leftTailLB_sound`: on `(0, 2^-30]`, `leftTailLB / 2^P ≤ F`;
* `rightTailLB_sound`: on `[21, ∞)`, `rightTailLB / 2^P ≤ F`.

Computed records and the large closed constants (`sNum`, `sumAbsC (mkRecs ..)`, the context fields) are kept opaque by
`generalize` before any tactic that could reduce them.
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-- `ℕ`-power with the instance of core Lean (as elaborated in `TPCore`), so that the restated checker terms below
are syntactically those of `TPCore` (no defeq check that could evaluate the certificate data). -/
local notation:75 a:76 " ^ᶜ " b:75 => @HPow.hPow ℕ ℕ ℕ (@instHPow ℕ ℕ (@instPowNat ℕ instNatPowNat)) a b

theorem cast_powC (a b : ℕ) : ((a ^ᶜ b : ℕ) : ℝ) = (a : ℝ) ^ b := Nat.cast_pow a b

/-! ## Constants of the budget -/

set_option maxRecDepth 20000 in
theorem cwSh_max : cwSh.foldl max 0 = 74 := by decide +kernel

set_option maxRecDepth 20000 in
theorem cwSh_le : ∀ j < 19, cwSh.getD j 0 ≤ 74 := by decide +kernel

set_option maxRecDepth 20000 in
theorem polys_zero : polys.getD 0 [] = [1, 0] := by decide +kernel

/-- The left side of the budget check (common denominator `2^S sDen`). -/
def lhsV : ℕ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (cwSh.foldl max 0 - x.2.2) * sDen) 0 +
    2 * sNum * 2 ^ᶜ (cwSh.foldl max 0)

/-- The common denominator `2^S sDen`. -/
def kDenV : ℕ := 2 ^ᶜ (cwSh.foldl max 0) * sDen

theorem budgetOK_iff : budgetOK = true ↔ lhsV < kDenV := by
  simp only [budgetOK, lhsV, kDenV, decide_eq_true_eq]

theorem kDenV_pos : (0 : ℝ) < (kDenV : ℝ) := by
  have h : 0 < kDenV := Nat.mul_pos (Nat.two_pow_pos _) sDen_pos
  exact_mod_cast h

/-- The budget sum with the large constants as parameters (keeps the kernel away from `sDen`, `sNum`). -/
theorem lhs_gen (S sD sN : ℕ) :
    (List.zip polys (List.zip cwNum cwSh)).foldl
      (fun acc x => acc + x.2.1 * (x.1.length - 1) * 2 ^ᶜ (S - x.2.2) * sD) 0 + 2 * sN * 2 ^ᶜ S =
    ∑ j ∈ Finset.range 19, cwNum.getD j 0 * ((polys.getD j []).length - 1) * 2 ^ᶜ (S - cwSh.getD j 0) * sD +
      2 * sN * 2 ^ᶜ S := by
  have hsum : ∀ (g : ℕ → ℕ), ((List.range 19).map g).sum = ∑ j ∈ Finset.range 19, g j :=
    fun g => list_sum_range g 19
  rw [polyZip_eq, foldl_add_eq_sum, zero_add, List.map_map, hsum]
  rfl

theorem lhsV_eq : lhsV =
    ∑ j ∈ Finset.range 19, cwNum.getD j 0 * ((polys.getD j []).length - 1) *
      2 ^ᶜ (cwSh.foldl max 0 - cwSh.getD j 0) * sDen + 2 * sNum * 2 ^ᶜ (cwSh.foldl max 0) :=
  lhs_gen _ _ _

/-- `lhs / (2^S sDen) = ∑ cⱼ dⱼ + 2 s`. -/
theorem lhsV_div : (lhsV : ℝ) / (kDenV : ℝ) =
    ∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) + 2 * sR := by
  have hD : (0 : ℝ) < (sDen : ℝ) := by exact_mod_cast sDen_pos
  have hle : ∀ j < 19, cwSh.getD j 0 ≤ cwSh.foldl max 0 := by
    rw [cwSh_max]
    exact cwSh_le
  rw [lhsV_eq, kDenV, sR_eq]
  generalize cwSh.foldl max 0 = S at hle ⊢
  generalize sNum = sN
  generalize sDen = sD at hD ⊢
  have hS : (0 : ℝ) < 2 ^ S := by positivity
  push_cast [cast_powC]
  rw [div_eq_iff (mul_pos hS hD).ne', add_mul, Finset.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [pow_sub₀ (2 : ℝ) two_ne_zero (hle j (Finset.mem_range.mp hj))]
    unfold cj
    field_simp
  · field_simp

/-- **The degree budget.** -/
theorem budget_sound (h : budgetOK = true) :
    ∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) + 2 * sR < 1 := by
  rw [budgetOK_iff] at h
  rw [← lhsV_div, div_lt_one kDenV_pos]
  exact_mod_cast h


/-! ## A generic fold: the `j = 0` term and the others -/

theorem foldl_ite_add {α : Type*} (p : α → Prop) [DecidablePred p] (f g : α → ℤ) :
    ∀ (l : List α) (a : ℤ), l.foldl (fun acc y => if p y then acc + f y else acc + g y) a =
      a + (l.map (fun y => if p y then f y else g y)).sum
  | [], a => by simp
  | y :: ys, a => by
    rw [List.foldl_cons, foldl_ite_add p f g ys, List.map_cons, List.sum_cons]
    by_cases h : p y
    · simp only [h, ite_true]
      ring
    · simp only [h, ite_false]
      ring

theorem foldl_zipIdx_split {α : Type*} (A B : α → ℤ) (u : ℕ → α) (n : ℕ) (a : ℤ) :
    ((List.range (n + 1)).map (fun j => (u j, j))).foldl
      (fun acc x => if x.2 = 0 then acc + A x.1 else acc + B x.1) a =
      a + A (u 0) + ∑ j ∈ Finset.range n, B (u (j + 1)) := by
  rw [foldl_ite_add (fun x : α × ℕ => x.2 = 0) (fun x => A x.1) (fun x => B x.1), List.map_map,
    list_sum_range, Finset.sum_range_succ']
  simp only [Function.comp_apply, Nat.add_one_ne_zero, ite_false, ite_true]
  ring

/-! ## The left tail -/

/-- The term of `Q₀ = x` in `leftTailLB`. -/
def ltA (X0 D : ℕ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * (logT TAB L2 X0 D).2) (2 ^ z.2.2)

/-- The term of `Qⱼ`, `j ≥ 1`, in `leftTailLB`. -/
def ltB (X0 D : ℕ) (LD : ℤ × ℤ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * ((logT TAB L2 (max (encl X0 (taylorR 0 D z.1)).1.natAbs
    (encl X0 (taylorR 0 D z.1)).2.natAbs) 1).2 - ((z.1.length - 1 : Nat) : Int) * LD.1)) (2 ^ z.2.2)

/-- The polynomial part of `leftTailLB`. -/
def polyPartL (X0 D : ℕ) (LD : ℤ × ℤ) : ℤ :=
  (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
    (fun (acc : Int) (x : (List Int × Nat × Nat) × Nat) =>
      if x.2 = 0 then acc + ltA X0 D x.1 else acc + ltB X0 D LD x.1) 0

theorem leftTailLB_eq (X0 k : ℕ) : leftTailLB (mkCtx iLoNum 128) X0 k =
    (mkCtx iLoNum 128).isLo - (mkCtx iLoNum 128).m0hi +
      polyPartL X0 (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) -
      2 * (uHi (pointPass TAB L2 (mkRecs GS nodes gvals) k 0 (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
        cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * X0 : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS)) := by
  simp only [leftTailLB, polyPartL, ltA, ltB, ctx_tab, ctx_l2, ctx_rs, ctx_sumC]

theorem ltA_le {X0 D : ℕ} (hX0 : 0 < X0) (hD : 0 < D) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (X0 : ℝ) / D)
    (desc : List ℤ) (cn cs : ℕ) :
    (ltA X0 D (desc, cn, cs) : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR [1, 0]).eval x|) :=
  leftTail_x_term logT_all hX0 hD hx0 hx cn cs

theorem ltB_le {X0 D : ℕ} (hD : 0 < D) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (X0 : ℝ) / D) (desc : List ℤ) (hQ : (QR desc).eval x ≠ 0) (cn cs : ℕ) :
    (ltB X0 D LD (desc, cn, cs) : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval x|) := by
  have h0 : ((0 : ℕ) : ℝ) / D ≤ x := by rw [Nat.cast_zero, zero_div]; exact hx0.le
  have h1 : x ≤ (((0 : ℕ) : ℝ) + X0) / D := by rw [Nat.cast_zero, zero_add]; exact hx
  exact encl_log_term logT_all hLD hD 0 X0 desc h0 h1 hQ cn cs

theorem polyPartL_le {X0 D : ℕ} (hX0 : 0 < X0) (hD : 0 < D) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (X0 : ℝ) / D) (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (polyPartL X0 D LD : ℝ) ≤
      2 ^ P * -∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| := by
  unfold polyPartL
  rw [polyList_eq, foldl_zipIdx_split (ltA X0 D) (ltB X0 D LD)
    (fun j => (polys.getD j [], cwNum.getD j 0, cwSh.getD j 0)) 18 0]
  rw [Finset.sum_range_succ' _ 18, zero_add, Int.cast_add, Int.cast_sum]
  have hA := ltA_le hX0 hD hx0 hx (polys.getD 0 []) (cwNum.getD 0 0) (cwSh.getD 0 0)
  have hB : ∀ j ∈ Finset.range 18,
      (ltB X0 D LD (polys.getD (j + 1) [], cwNum.getD (j + 1) 0, cwSh.getD (j + 1) 0) : ℝ) ≤
        2 ^ P * -(cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x|) := by
    intro j hj
    have h := ltB_le hD hLD hx0 hx (polys.getD (j + 1) []) (hQx (j + 1) (by
      have := Finset.mem_range.mp hj
      omega)) (cwNum.getD (j + 1) 0) (cwSh.getD (j + 1) 0)
    refine le_trans h (le_of_eq ?_)
    unfold cj
    ring
  have hsB := Finset.sum_le_sum hB
  rw [polys_zero] at hA ⊢
  have e : 2 ^ P * (-((cwNum.getD 0 0 : ℕ) / 2 ^ (cwSh.getD 0 0) : ℝ) * Real.log |(QR [1, 0]).eval x|) =
      2 ^ P * -(cj 0 * Real.log |(QR [1, 0]).eval x|) := by
    unfold cj
    ring
  rw [e] at hA
  have e2 : 2 ^ P * -(∑ j ∈ Finset.range 18, cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x| +
      cj 0 * Real.log |(QR [1, 0]).eval x|) =
      ∑ j ∈ Finset.range 18, 2 ^ P * -(cj (j + 1) * Real.log |(QR (polys.getD (j + 1) [])).eval x|) +
        2 ^ P * -(cj 0 * Real.log |(QR [1, 0]).eval x|) := by
    rw [neg_add, mul_add, ← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [e2]
  linarith

/-- **The left tail** `(0, 2^-30]`. -/
theorem leftTailLB_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (DEC : ℝ) / (DEC * 2 ^ 30 : ℕ)) (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (leftTailLB (mkCtx iLoNum 128) DEC 30 : ℝ) / 2 ^ P ≤ FR x := by
  have hD : 0 < DEC * 2 ^ 30 := Nat.mul_pos (by decide) (Nat.two_pow_pos 30)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ 30 : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hQS : (0 : ℝ) < 2 ^ QS := by positivity
  have hX0 : 0 < DEC := by decide
  rw [leftTailLB_eq]
  have hLDs := logT_D 30
  have hU0 : 2 ^ P * UR (((0 : ℕ) : ℝ) / (DEC * 2 ^ 30 : ℕ)) ≤
      (uHi (pointPass TAB L2 (mkRecs GS nodes gvals) 30 0 (logT TAB L2 (DEC * 2 ^ 30) 1)) (DEC * 2 ^ 30) : ℝ) :=
    uHi_le_of hD (pointPass_sound (X := 0) hLDs).2
  rw [Nat.cast_zero, zero_div] at hU0
  have hpp := polyPartL_le hX0 hD hLDs hx0 hx hQx
  have hsC := sumC_ge
  have hdU := le_cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * DEC : ℕ) : ℤ) * 2 ^ P)
    (b := DEC * 2 ^ 30 * 2 ^ QS) (Nat.mul_pos hD (Nat.two_pow_pos QS))
  generalize uHi (pointPass TAB L2 (mkRecs GS nodes gvals) 30 0 (logT TAB L2 (DEC * 2 ^ 30) 1)) (DEC * 2 ^ 30) = uh
    at hU0 ⊢
  generalize polyPartL DEC (DEC * 2 ^ 30) (logT TAB L2 (DEC * 2 ^ 30) 1) = pp at hpp ⊢
  generalize cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * DEC : ℕ) : ℤ) * 2 ^ P)
    (DEC * 2 ^ 30 * 2 ^ QS) = dU at hdU ⊢
  generalize sumAbsC (mkRecs GS nodes gvals) = sC at hsC hdU
  set D : ℕ := DEC * 2 ^ 30 with hDdef
  set SC : ℝ := ∑ i ∈ Finset.range (NN + 1), |CR i| with hSC
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hx22 : x ≤ 22 := by
    refine le_trans hx ?_
    rw [div_le_iff₀ hDR]
    have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hdec : (DEC : ℝ) = 10000000000 := by unfold DEC; norm_num
    have hDv : (D : ℝ) = (DEC : ℝ) * 2 ^ 30 := by rw [hDdef]; push_cast; ring
    rw [hDv, hdec]
    norm_num
  -- the potential moves by at most `47 ∑ |Cᵢ| x₀`
  have hUx : UR x ≤ UR 0 + 47 * SC * ((DEC : ℝ) / D) := by
    have h : UR x ≤ UR 0 + 47 * SC * |x - 0| :=
      UR_le_add (abs_eR_sub_le hx0.le hx22) (abs_eR_sub_le le_rfl (by norm_num))
    rw [sub_zero, abs_of_pos hx0] at h
    have := mul_le_mul_of_nonneg_left hx (mul_nonneg (by norm_num : (0 : ℝ) ≤ 47) hSC0)
    linarith
  have hdU' : 2 ^ P * (47 * SC * ((DEC : ℝ) / D)) ≤ (dU : ℝ) := by
    refine le_trans ?_ hdU
    have hDQ : ((D * 2 ^ QS : ℕ) : ℝ) = (D : ℝ) * 2 ^ QS := by push_cast; ring
    rw [hDQ, le_div_iff₀ (mul_pos hDR hQS)]
    have e : 2 ^ P * (47 * SC * ((DEC : ℝ) / D)) * ((D : ℝ) * 2 ^ QS) =
        47 * (2 ^ QS * SC) * (DEC : ℝ) * 2 ^ P := by field_simp
    rw [e]
    push_cast
    have h47 : (0 : ℝ) ≤ 47 * (DEC : ℝ) * 2 ^ P :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hP.le
    nlinarith
  have hpl : (0 : ℝ) ≤ Real.posLog x := Real.posLog_nonneg
  have h2 := isLo_le hI
  have h3 := m0hi_ge
  have hFR : FR x = Real.posLog x - m0 - ∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| -
      2 * UR x + IR / sR := by
    unfold FR; rw [FR_poly_sum]
  rw [hFR, div_le_iff₀ hP]
  push_cast
  have hUxP := mul_le_mul_of_nonneg_left hUx hP.le
  nlinarith


/-! ## The right tail -/

/-- `κ · 2^S sDen`, `κ = 1 - ∑ cⱼ dⱼ - 2 s` (`kNum` of `rightTailLB`). -/
def kNumV : ℤ := (kDenV : ℤ) - (lhsV : ℤ)

/-- `klog` of `rightTailLB` as a function of `kNum`, `kDen`. -/
def klogF (kN : ℤ) (kD Xt : ℕ) : ℤ :=
  if 0 ≤ kN then fdiv (kN * (logT TAB L2 Xt DEC).1) kD else fdiv (kN * (logT TAB L2 Xt DEC).2) kD

/-- `klog` of `rightTailLB`. -/
def klogV (Xt : ℕ) : ℤ := klogF kNumV kDenV Xt

/-- The term of one polynomial in `rightTailLB`. -/
def rtA (Xt : ℕ) (z : List Int × ℕ × ℕ) : ℤ :=
  fdiv (-(z.2.1 : Int) * (logT TAB L2
    (z.1.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ᶜ q.2 * Xt ^ᶜ (z.1.length - 1 - q.2)) 0)
    (Xt ^ᶜ (z.1.length - 1))).2) (2 ^ᶜ z.2.2)

/-- The polynomial part of `rightTailLB`. -/
def aPartR (Xt : ℕ) : ℤ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl (fun (acc : Int) (x : List Int × Nat × Nat) => acc + rtA Xt x) 0

theorem rightTailLB_eq (Xt : ℕ) : rightTailLB (mkCtx iLoNum 128) Xt =
    klogV Xt - (mkCtx iLoNum 128).m0hi + (mkCtx iLoNum 128).isLo + aPartR Xt := by
  simp only [rightTailLB, klogV, klogF, kNumV, kDenV, lhsV, aPartR, rtA, ctx_tab, ctx_l2]
  -- the two sides differ only in the `Decidable` instance of the `if` (`Int.decLe 0 kNumV` against its unfolding)
  congr 3

theorem foldl_map_range_add {α : Type*} (h : ℕ → α) (g : α → ℤ) (n : ℕ) :
    ((List.range n).map h).foldl (fun acc y => acc + g y) 0 = ∑ j ∈ Finset.range n, g (h j) := by
  rw [foldl_add_eq_sum, zero_add, List.map_map, list_sum_range]
  rfl

theorem rtA_le {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x) (desc : List ℤ)
    (hQ : (QR desc).eval x ≠ 0) (cn cs : ℕ) :
    (rtA Xt (desc, cn, cs) : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(QR desc).eval x| - (desc.length - 1 : ℕ) * Real.log x)) :=
  rightTail_poly_term logT_all desc hXt hx hQ cn cs

theorem aPartR_le {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x)
    (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (aPartR Xt : ℝ) ≤ 2 ^ P * ∑ j ∈ Finset.range 19, -(cj j * (Real.log |(QR (polys.getD j [])).eval x| -
      (((polys.getD j []).length - 1 : ℕ) : ℝ) * Real.log x)) := by
  unfold aPartR
  rw [polyZip_eq, foldl_map_range_add, Int.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := rtA_le hXt hx (polys.getD j []) (hQx j (Finset.mem_range.mp hj)) (cwNum.getD j 0) (cwSh.getD j 0)
  refine le_trans h (le_of_eq ?_)
  unfold cj
  ring

theorem klogV_le {Xt : ℕ} (hXt : 0 < Xt) :
    (klogV Xt : ℝ) ≤ 2 ^ P * ((kNumV : ℝ) / kDenV * Real.log ((Xt : ℝ) / DEC)) := by
  have hl := logT_all Xt DEC hXt (by decide)
  have hK := kDenV_pos
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold klogV klogF
  generalize kNumV = kN
  generalize kDenV = kD at hK ⊢
  generalize logT TAB L2 Xt DEC = lx at hl ⊢
  have hKn : 0 < kD := by exact_mod_cast hK
  have e : 2 ^ P * ((kN : ℝ) / kD * Real.log ((Xt : ℝ) / DEC)) * kD =
      (kN : ℝ) * (2 ^ P * Real.log ((Xt : ℝ) / DEC)) := by
    field_simp
  split_ifs with h
  · have h1 := fdiv_le (kN * lx.1) hKn
    refine h1.trans ?_
    rw [div_le_iff₀ hK, e]
    have hk : (0 : ℝ) ≤ kN := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_left hl.1 hk
    push_cast
    linarith
  · have h1 := fdiv_le (kN * lx.2) hKn
    refine h1.trans ?_
    rw [div_le_iff₀ hK, e]
    have hk : (kN : ℝ) ≤ 0 := by
      have : kN < 0 := lt_of_not_ge h
      exact_mod_cast this.le
    have := mul_le_mul_of_nonpos_left hl.2 hk
    push_cast
    linarith

theorem kappa_eq : (kNumV : ℝ) / kDenV =
    1 - (∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) + 2 * sR) := by
  rw [← lhsV_div]
  unfold kNumV
  have hK := kDenV_pos
  generalize lhsV = L
  generalize kDenV = kD at hK ⊢
  push_cast
  field_simp

/-- **The right tail** `[21, ∞)`. -/
theorem rightTailLB_sound (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) (hb : budgetOK = true) {x : ℝ}
    (hx : ((XT * DEC : ℕ) : ℝ) / DEC ≤ x) (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (rightTailLB (mkCtx iLoNum 128) (XT * DEC) : ℝ) / 2 ^ P ≤ FR x := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hXt : 0 < XT * DEC := by decide
  have hxt : (112 / 10 : ℝ) ≤ ((XT * DEC : ℕ) : ℝ) / DEC := by
    unfold XT DEC
    norm_num
  have hxt1 : (1 : ℝ) ≤ ((XT * DEC : ℕ) : ℝ) / DEC := le_trans (by norm_num) hxt
  have hx1 : (1 : ℝ) ≤ x := le_trans hxt1 hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  rw [rightTailLB_eq]
  have hk := klogV_le hXt
  have ha := aPartR_le hXt hx hQx
  have hbud := budget_sound hb
  have hkap := kappa_eq
  have hU : UR x ≤ sR * Real.log x := UR_le_sR_log (le_trans (eR_range le_rfl).2 (le_trans hxt hx))
  have hlog : Real.log (((XT * DEC : ℕ) : ℝ) / DEC) ≤ Real.log x :=
    Real.log_le_log (lt_of_lt_of_le one_pos hxt1) hx
  have h2 := isLo_le hI
  have h3 := m0hi_ge
  generalize klogV (XT * DEC) = kl at hk ⊢
  generalize aPartR (XT * DEC) = ap at ha ⊢
  rw [hkap] at hk
  set Dd : ℝ := ∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) with hDd
  set A : ℝ := ∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| with hA
  have hsplit : ∑ j ∈ Finset.range 19, -(cj j * (Real.log |(QR (polys.getD j [])).eval x| -
      (((polys.getD j []).length - 1 : ℕ) : ℝ) * Real.log x)) = -A + Dd * Real.log x := by
    rw [hA, hDd, Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hsplit] at ha
  have hkap0 : 0 ≤ 1 - (Dd + 2 * sR) := by linarith
  have hk2 : (kl : ℝ) ≤ 2 ^ P * ((1 - (Dd + 2 * sR)) * Real.log x) := by
    refine hk.trans ?_
    have := mul_le_mul_of_nonneg_left hlog hkap0
    exact mul_le_mul_of_nonneg_left this hP.le
  have hFR : FR x = Real.posLog x - m0 - A - 2 * UR x + IR / sR := by
    unfold FR
    rw [FR_poly_sum]
  rw [hFR, posLog_eq_log_of_one_le hx1, div_le_iff₀ hP]
  push_cast
  have e1 : 2 ^ P * ((1 - (Dd + 2 * sR)) * Real.log x) =
      2 ^ P * Real.log x - 2 ^ P * (Dd * Real.log x) - 2 * (2 ^ P * (sR * Real.log x)) := by ring
  have e2 : 2 ^ P * (-A + Dd * Real.log x) = -(2 ^ P * A) + 2 ^ P * (Dd * Real.log x) := by ring
  have hU2 : 2 ^ P * UR x ≤ 2 ^ P * (sR * Real.log x) := mul_le_mul_of_nonneg_left hU hP.le
  have e3 : (Real.log x - m0 - A - 2 * UR x + IR / sR) * 2 ^ P =
      2 ^ P * Real.log x - 2 ^ P * m0 - 2 ^ P * A - 2 * (2 ^ P * UR x) + 2 ^ P * (IR / sR) := by ring
  rw [e1] at hk2
  rw [e2] at ha
  rw [e3]
  linarith

end TPMahler.Cert
