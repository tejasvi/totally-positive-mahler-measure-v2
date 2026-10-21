import AuxCommon.Basic

/-!
# Northcott's theorem for bounded degree (finiteness part)

* `finite_minpolyZ_bounded`: for every `n` and `B` only finitely many `α : ℂ` have a minimal polynomial `P` over `ℤ`
  with `deg P ≤ n` and `M(P) ≤ B` (from Mathlib's `Polynomial.finite_mahlerMeasure_le`: finitely many `P`, each with
  finitely many roots).
* `log_mahlerMeasure_nonneg`: `log M(P) ≥ 0` for `P ≠ 0` in `ℤ[X]` (Mathlib `one_le_mahlerMeasure_of_ne_zero`).
* `finite_setOf_exists_aeval_eq_zero`: the roots of finitely many nonzero integer polynomials form a finite set.
* `exists_error_lt`: the error term `λ (1 + log (2Kn)) / n` of Lemma 2.2 of both papers is eventually `< ε`.
-/

open Polynomial Filter Topology

namespace AuxCommon

/-- `log M(P) ≥ 0` for a nonzero integer polynomial. -/
theorem log_mahlerMeasure_nonneg {P : ℤ[X]} (hP : P ≠ 0) : 0 ≤ Real.log (toC P).mahlerMeasure :=
  Real.log_nonneg (one_le_mahlerMeasure_of_ne_zero hP)

/-- The complex roots of a nonzero integer polynomial form a finite set. -/
theorem finite_setOf_aeval_eq_zero {Q : ℤ[X]} (hQ : Q ≠ 0) : {z : ℂ | aeval z Q = 0}.Finite := by
  have hQ' : toC Q ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hQ
  refine ((toC Q).roots.toFinset.finite_toSet).subset ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ', IsRoot.def, eval_map, ← algebraMap_int_eq,
    ← aeval_def]
  exact hz

/-- The roots of finitely many nonzero integer polynomials form a finite set. -/
theorem finite_setOf_exists_aeval_eq_zero {J : ℕ} (Q : Fin J → ℤ[X]) (hQ : ∀ j, Q j ≠ 0) :
    {z : ℂ | ∃ j, aeval z (Q j) = 0}.Finite := by
  have : {z : ℂ | ∃ j, aeval z (Q j) = 0} = ⋃ j, {z : ℂ | aeval z (Q j) = 0} := by
    ext z
    simp
  rw [this]
  exact Set.finite_iUnion fun j => finite_setOf_aeval_eq_zero (hQ j)

/-- **Northcott's theorem for bounded degree.** Only finitely many algebraic numbers have a minimal polynomial over
`ℤ` of degree at most `n` and Mahler measure at most `B`. -/
theorem finite_minpolyZ_bounded (n : ℕ) (B : ℝ) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ P.natDegree ≤ n ∧ (toC P).mahlerMeasure ≤ B}.Finite := by
  have hS := finite_mahlerMeasure_le n B.toNNReal
  refine (hS.biUnion fun P _ => ((toC P).roots.toFinset.finite_toSet)).subset ?_
  rintro α ⟨P, hP, hdeg, hM⟩
  rw [Set.mem_iUnion₂]
  refine ⟨P, ⟨hdeg, hM.trans ?_⟩, ?_⟩
  · rw [Real.coe_toNNReal']
    exact le_max_left _ _
  · have hP0 : P ≠ 0 := by
      rintro rfl
      exact (lt_irrefl 0) (by simpa using hP.2.1)
    have hP' : toC P ≠ 0 := (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hP0
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hP', IsRoot.def, eval_map,
      ← algebraMap_int_eq, ← aeval_def]
    exact hP.2.2

/-- `0 < deg P ≤ n` and `log M(P) / deg P ≤ B` give `M(P) ≤ exp (n max(B, 0))`. -/
theorem mahlerMeasure_le_exp {P : ℤ[X]} (hP0 : P ≠ 0) (hpos : 0 < P.natDegree) {n : ℕ}
    (hdeg : P.natDegree ≤ n) {B : ℝ} (hB : Real.log (toC P).mahlerMeasure / P.natDegree ≤ B) :
    (toC P).mahlerMeasure ≤ Real.exp (n * max B 0) := by
  have hn : (0 : ℝ) < P.natDegree := by exact_mod_cast hpos
  have hMpos : 0 < (toC P).mahlerMeasure :=
    lt_of_lt_of_le zero_lt_one (one_le_mahlerMeasure_of_ne_zero hP0)
  rw [div_le_iff₀ hn] at hB
  rw [← Real.exp_log hMpos, Real.exp_le_exp]
  calc Real.log (toC P).mahlerMeasure ≤ B * P.natDegree := hB
    _ ≤ max B 0 * P.natDegree := by gcongr; exact le_max_left _ _
    _ ≤ max B 0 * n := by gcongr
    _ = n * max B 0 := mul_comm _ _

/-- Northcott for bounded degree and bounded `log M(P) / deg P`. -/
theorem finite_minpolyZ_logHeight_le (n : ℕ) (B : ℝ) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ P.natDegree ≤ n ∧
      Real.log (toC P).mahlerMeasure / P.natDegree ≤ B}.Finite := by
  refine (finite_minpolyZ_bounded n (Real.exp (n * max B 0))).subset ?_
  rintro α ⟨P, hP, hdeg, hB⟩
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact (lt_irrefl 0) (by simpa using hP.2.1)
  exact ⟨P, hP, hdeg, mahlerMeasure_le_exp hP0 hP.2.1 hdeg hB⟩

/-- Finitely many integer polynomials of degree `≤ n` with `log M(P) / deg P ≤ B` and positive degree. -/
theorem finite_poly_logHeight_le (n : ℕ) (B : ℝ) :
    {P : ℤ[X] | P ≠ 0 ∧ 0 < P.natDegree ∧ P.natDegree ≤ n ∧
      Real.log (toC P).mahlerMeasure / P.natDegree ≤ B}.Finite := by
  refine (finite_mahlerMeasure_le n (Real.exp (n * max B 0)).toNNReal).subset ?_
  rintro P ⟨hP0, hpos, hdeg, hB⟩
  refine ⟨hdeg, (mahlerMeasure_le_exp hP0 hpos hdeg hB).trans ?_⟩
  rw [Real.coe_toNNReal']
  exact le_max_left _ _

/-- The error term `λ (1 + log (2Kn)) / n` tends to `0`: it is `< ε` for all large `n`. -/
theorem exists_error_lt (lam K ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → lam * (1 + Real.log (2 * K * n)) / n < ε := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h3 : Tendsto (fun x : ℝ => lam * ((1 + Real.log (2 * K)) * x⁻¹ + Real.log x / x)) atTop
      (𝓝 (lam * ((1 + Real.log (2 * K)) * 0 + 0))) :=
    (h2.const_mul _).add h1 |>.const_mul lam
  rw [mul_zero, zero_add, mul_zero] at h3
  have h4 : ∀ᶠ x : ℝ in atTop, lam * (1 + Real.log (2 * K * x)) / x =
      lam * ((1 + Real.log (2 * K)) * x⁻¹ + Real.log x / x) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [Real.log_mul (by positivity) hx.ne']
    field_simp
    ring
  have h5 := (h3.congr' (h4.mono fun x hx => hx.symm)).eventually (gt_mem_nhds hε)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp h5
  refine ⟨⌈x₀⌉₊, fun n hn => hx₀ n ?_⟩
  exact (Nat.le_ceil x₀).trans (by exact_mod_cast hn)

end AuxCommon
