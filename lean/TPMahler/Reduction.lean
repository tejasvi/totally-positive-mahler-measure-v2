import AuxCommon.Averaging
import AuxCommon.Northcott
import TPMahler.Statement

/-!
# Reduction of Theorem 1.1 to the auxiliary inequality

* `lemma22`: Lemma 2.2 of the paper (lem:aux), the effective bound
  `log Ω(α) ≥ m - λ (1 + log (2Kn)) / n` for totally positive `α` of degree `n ≥ 1/(2K)` that is not a root of a `Qⱼ`,
  from the auxiliary inequality `F ≥ 0` on `(0, ∞)`, the degree condition `∑ cⱼ deg Qⱼ + 2λ ≤ 1` and the named
  hypothesis `EnergySmoothing`.
* `cor23`: Corollary 2.3 (cor:fin), `TPLow (m - ε)` is finite.
* Forms of the top theorems with the hypotheses of `cor23` as parameters: `omega_finite` (finiteness of
  `{α totally positive : Ω(α) ≤ B}` for `log B < m`), `finite_Lplus_le` and `exp_le_of_accPt_Lplus`
  (every accumulation point of `𝓛₊` is at least `e^m`).
-/

open Polynomial MeasureTheory Filter Topology
open AuxCommon

namespace TPMahler

/-- `log Ω(α) ≥ 0` (for every `P : ℤ[X]`; `logOmega 0 = 0`). -/
theorem logOmega_nonneg (P : ℤ[X]) : 0 ≤ logOmega P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [logOmega]
  · exact div_nonneg (log_mahlerMeasure_nonneg hP) (Nat.cast_nonneg _)

set_option linter.unusedVariables false in
/-- **Lemma 2.2 of the paper** (lem:aux, inequality (2.3)). The hypothesis `hQ` is implied by `hnr`; it is kept so that
`lemma22` and `cor23` take the same hypotheses. -/
theorem lemma22 (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hbudget : ∑ j, c j * (Q j).natDegree + 2 * lam ≤ 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ Real.posLog x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    {P : ℤ[X]} {α : ℂ} (hP : IsMinpolyZ P α) (hpos : AllRootsPos P) (hnr : ∀ j, aeval α (Q j) ≠ 0)
    (hn : 1 / (2 * K) ≤ P.natDegree) :
    m - lam * (1 + Real.log (2 * K * P.natDegree)) / P.natDegree ≤ logOmega P := by
  classical
  have hnR : (0 : ℝ) < P.natDegree := by exact_mod_cast hP.2.1
  have hcard : (rootsC P).card = P.natDegree := hP.card_rootsC
  -- Step 1: the auxiliary inequality at each conjugate (a positive real number)
  have hle : ∀ β ∈ rootsC P, m + ∑ j, c j * Real.log ‖eval β (toC (Q j))‖ +
      lam * (2 * logPot ν β - logEnergy ν) ≤ Real.posLog ‖β‖ := by
    intro β hβ
    obtain ⟨h1, h2⟩ := hpos β (Multiset.mem_toFinset.mp hβ)
    have hβre : ((β.re : ℝ) : ℂ) = β := Complex.ext (by simp) (by simp [h2])
    have hnorm : ‖β‖ = β.re := by
      conv_lhs => rw [← hβre]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1]
    have := hF β.re h1 (fun j => by rw [hβre]; exact hP.eval_ne_zero_of_mem_rootsC (hnr j) hβ)
    rw [hβre] at this
    rw [hnorm]
    linarith
  -- Step 2: sum over the conjugates
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hcard, nsmul_eq_mul,
    Finset.sum_comm, ← Finset.mul_sum] at hsum
  simp only [← Finset.mul_sum] at hsum
  -- Step 3: the resultant bound (A1)
  have hA : -((∑ j, c j * ((Q j).natDegree : ℝ)) * Real.log |(P.leadingCoeff : ℝ)|) ≤
      ∑ j, c j * ∑ β ∈ rootsC P, Real.log ‖eval β (toC (Q j))‖ := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h1 := mul_le_mul_of_nonneg_left (hP.sum_log_norm_eval_ge (hnr j)) (hc j)
    linarith
  -- Step 4: energy smoothing with r = 1/(2Kn) and the discriminant bound (A2)
  have hEb := hP.energy_sum_ge hE ν hK hsupp hdisc hn
  -- Step 5: combine with n log Ω = log |a| + ∑ log⁺ αᵢ
  have hlamE := mul_le_mul_of_nonneg_left hEb hlam
  have hLaC : 0 ≤ Real.log |(P.leadingCoeff : ℝ)| * (1 - ∑ j, c j * ((Q j).natDegree : ℝ) - 2 * lam) :=
    mul_nonneg hP.log_abs_leadingCoeff_nonneg (by linarith)
  rw [logOmega, hP.log_mahlerMeasure_eq, le_div_iff₀ hnR, sub_mul, div_mul_cancel₀ _ hnR.ne']
  nlinarith

/-- **Corollary 2.3 of the paper** (cor:fin): for every `ε > 0` only finitely many totally positive algebraic numbers
satisfy `log Ω(α) ≤ m - ε`. -/
theorem cor23 (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hbudget : ∑ j, c j * (Q j).natDegree + 2 * lam ≤ 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ Real.posLog x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    (ε : ℝ) (hε : 0 < ε) : (TPLow (m - ε)).Finite := by
  obtain ⟨n₀, hn₀⟩ := exists_error_lt lam K ε hK hε
  refine ((finite_setOf_exists_aeval_eq_zero Q hQ).union
    (finite_minpolyZ_logHeight_le (max n₀ ⌈1 / (2 * K)⌉₊) (m - ε))).subset ?_
  rintro α ⟨P, hP, hpos, hlow⟩
  by_cases hroot : ∃ j, aeval α (Q j) = 0
  · exact Or.inl hroot
  · refine Or.inr ?_
    push Not at hroot
    refine ⟨P, hP, ?_, hlow⟩
    by_contra hdeg
    push Not at hdeg
    have hn1 : 1 / (2 * K) ≤ P.natDegree :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hdeg.le)
    have h22 := lemma22 hE Q c lam m K ν hQ hc hlam hK hsupp hdisc hbudget hF hP hpos hroot hn1
    have herr := hn₀ P.natDegree ((le_max_left _ _).trans hdeg.le)
    have hlow' : logOmega P ≤ m - ε := hlow
    linarith

/-- `Ω(α) ≤ B` gives `log Ω(α) ≤ log B`. -/
theorem logOmega_le_log {P : ℤ[X]} (hP0 : P ≠ 0) {B : ℝ}
    (hB : (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) ≤ B) : logOmega P ≤ Real.log B := by
  have hM : 0 < (toC P).mahlerMeasure :=
    lt_of_lt_of_le zero_lt_one (one_le_mahlerMeasure_of_ne_zero hP0)
  have h := Real.log_le_log (Real.rpow_pos_of_pos hM _) hB
  rw [Real.log_rpow hM] at h
  rw [logOmega, div_eq_inv_mul]
  exact h

/-- `Ω(α) ≥ 1`. -/
theorem one_le_omega {P : ℤ[X]} (hP0 : P ≠ 0) :
    1 ≤ (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) :=
  Real.one_le_rpow (one_le_mahlerMeasure_of_ne_zero hP0) (by positivity)

/-- **Form (b) of Theorem 1.1, generic.** Under the hypotheses of `cor23`, only finitely many totally positive
algebraic numbers satisfy `Ω(α) ≤ B`, for every `B` with `log B < m`. -/
theorem omega_finite (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hbudget : ∑ j, c j * (Q j).natDegree + 2 * lam ≤ 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ Real.posLog x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    (B : ℝ) (hB : Real.log B < m) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧
      (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) ≤ B}.Finite := by
  refine (cor23 hE Q c lam m K ν hQ hc hlam hK hsupp hdisc hbudget hF (m - Real.log B)
    (by linarith)).subset ?_
  rintro α ⟨P, hP, hpos, hle⟩
  refine ⟨P, hP, hpos, ?_⟩
  rw [sub_sub_cancel]
  exact logOmega_le_log hP.ne_zero hle

/-- Under the hypotheses of `cor23`, only finitely many values `Ω(α)` (`α` totally positive) lie below any
`y < e^m`. -/
theorem finite_Lplus_le (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ) (lam m K : ℝ)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j) (hlam : 0 ≤ lam)
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hbudget : ∑ j, c j * (Q j).natDegree + 2 * lam ≤ 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ Real.posLog x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν))
    (y : ℝ) (hy : y < Real.exp m) : {v ∈ Lplus | v ≤ y}.Finite := by
  rcases le_or_gt y 0 with hy0 | hy0
  · -- no value of `Ω` is `≤ 0`
    convert Set.finite_empty
    ext v
    simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    rintro ⟨α, -, P, hP, -, rfl⟩
    exact lt_of_lt_of_le (hy0.trans_lt zero_lt_one) (one_le_omega hP.ne_zero)
  have hlogy : Real.log y < m := (Real.log_lt_iff_lt_exp hy0).mpr hy
  obtain ⟨n₀, hn₀⟩ := exists_error_lt lam K (m - Real.log y) hK (by linarith)
  set N := max (max n₀ ⌈1 / (2 * K)⌉₊) (∑ j, (Q j).natDegree)
  refine ((finite_poly_logHeight_le N (Real.log y)).image
    (fun P : ℤ[X] => (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹))).subset ?_
  rintro v ⟨⟨α, -, P, hP, hpos, rfl⟩, hvy⟩
  have hlow := logOmega_le_log hP.ne_zero hvy
  refine ⟨P, ⟨hP.ne_zero, hP.2.1, ?_, hlow⟩, rfl⟩
  by_cases hroot : ∃ j, aeval α (Q j) = 0
  · obtain ⟨j, hj⟩ := hroot
    calc P.natDegree ≤ (Q j).natDegree := hP.natDegree_le_of_aeval_eq_zero (hQ j) hj
      _ ≤ ∑ j, (Q j).natDegree :=
        Finset.single_le_sum (f := fun j => (Q j).natDegree) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      _ ≤ N := le_max_right _ _
  · push Not at hroot
    by_contra hdeg
    push Not at hdeg
    have hn1 : 1 / (2 * K) ≤ P.natDegree :=
      (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans (le_max_left _ _)).trans hdeg.le)
    have h22 := lemma22 hE Q c lam m K ν hQ hc hlam hK hsupp hdisc hbudget hF hP hpos hroot hn1
    have herr := hn₀ P.natDegree (((le_max_left _ _).trans (le_max_left _ _)).trans hdeg.le)
    linarith

/-- **Form (c) of Theorem 1.1, generic.** Under the hypotheses of `cor23`, every accumulation point of `𝓛₊` is at
least `e^m`. -/
theorem exp_le_of_accPt_Lplus (hE : EnergySmoothing) {J : ℕ} (Q : Fin J → ℤ[X]) (c : Fin J → ℝ)
    (lam m K : ℝ) (ν : Measure ℂ) [IsProbabilityMeasure ν] (hQ : ∀ j, Q j ≠ 0) (hc : ∀ j, 0 ≤ c j)
    (hlam : 0 ≤ lam) (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K)
    (hbudget : ∑ j, c j * (Q j).natDegree + 2 * lam ≤ 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j, eval (x : ℂ) (toC (Q j)) ≠ 0) →
      0 ≤ Real.posLog x - m - ∑ j, c j * Real.log ‖eval (x : ℂ) (toC (Q j))‖ -
        lam * (2 * logPot ν x - logEnergy ν)) :
    ∀ y : ℝ, AccPt y (𝓟 Lplus) → Real.exp m ≤ y := by
  intro y hy
  by_contra hlt
  push Not at hlt
  set y' := (y + Real.exp m) / 2 with hy'_def
  have hyy' : y < y' := by rw [hy'_def]; linarith
  have hy' : y' < Real.exp m := by rw [hy'_def]; linarith
  have hfin := finite_Lplus_le hE Q c lam m K ν hQ hc hlam hK hsupp hdisc hbudget hF y' hy'
  set F := {v ∈ Lplus | v ≤ y'} with hF_def
  have hU : Set.Iio y' ∩ (F \ {y})ᶜ ∈ 𝓝 y :=
    Filter.inter_mem (Iio_mem_nhds hyy')
      ((hfin.sdiff).isClosed.isOpen_compl.mem_nhds (by simp))
  obtain ⟨z, ⟨⟨hzy', hzF⟩, hzL⟩, hzy⟩ := (accPt_iff_nhds.mp hy) _ hU
  exact hzF ⟨⟨hzL, le_of_lt hzy'⟩, hzy⟩

end TPMahler
