import AuxCommon.Basic

/-!
# Resultant and discriminant bounds

Let `P : ℤ[X]` be irreducible of positive degree `n` (a minimal polynomial over `ℤ`, `IsMinpolyZ P α`), with leading
coefficient `a`, and let `α₁, …, αₙ` be its complex roots (distinct, `rootsC P`).

* `IsMinpolyZ.sum_log_norm_eval_ge`: `∑ᵢ log |R(αᵢ)| ≥ -(deg R) log |a|` for every `R : ℤ[X]` with `R(α) ≠ 0`.
  The resultant `Res(P, R) = a^{deg R} ∏ᵢ R(αᵢ)` (Mathlib `Polynomial.resultant_eq_prod_eval`) is a nonzero integer.
* `IsMinpolyZ.sum_log_norm_sub_ge`: `∑_{i ≠ k} log |αᵢ - αₖ| ≥ -(2n - 2) log |a|`, and the weaker form
  `IsMinpolyZ.sum_log_norm_sub_ge'` with `2n - 1`. Here `Res(P, P') = a^{n-1} ∏ᵢ P'(αᵢ) = a^{2n-1} ∏_{i ≠ k} (αᵢ - αₖ)`
  and `Res(P, P') = ± a disc(P)` (Mathlib `Polynomial.resultant_deriv`), with `disc(P)` a nonzero integer.
-/

open Polynomial

namespace AuxCommon

/-- The complex roots of `P : ℤ[X]`, as a finset. -/
noncomputable abbrev rootsC (P : ℤ[X]) : Finset ℂ := (toC P).roots.toFinset

section basic

theorem eval_toC (R : ℤ[X]) (z : ℂ) : eval z (toC R) = aeval z R := by
  rw [aeval_def, eval_map, algebraMap_int_eq]

theorem natDegree_toC (P : ℤ[X]) : (toC P).natDegree = P.natDegree :=
  natDegree_map_eq_of_injective (RingHom.injective_int _) P

theorem leadingCoeff_toC (P : ℤ[X]) : (toC P).leadingCoeff = (P.leadingCoeff : ℂ) := by
  rw [leadingCoeff_map_of_injective (RingHom.injective_int _)]
  rfl

theorem toC_ne_zero {P : ℤ[X]} (hP : P ≠ 0) : toC P ≠ 0 :=
  (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hP

theorem card_roots_toC (P : ℤ[X]) : Multiset.card (toC P).roots = P.natDegree := by
  rw [← (IsAlgClosed.splits (toC P)).natDegree_eq_card_roots, natDegree_toC]

theorem toC_eq_map_rat (P : ℤ[X]) : toC P = (P.map (Int.castRingHom ℚ)).map (Rat.castHom ℂ) := by
  rw [Polynomial.map_map]
  congr 1

/-- `Res(P, R) = a^d ∏ᵢ R(αᵢ)` in `ℂ`, for any size `d ≥ deg R` of `R`. -/
theorem intCast_resultant (P R : ℤ[X]) (d : ℕ) (hd : R.natDegree ≤ d) :
    ((P.resultant R P.natDegree d : ℤ) : ℂ) =
      (P.leadingCoeff : ℂ) ^ d * ((toC P).roots.map (fun β => eval β (toC R))).prod := by
  have h1 := resultant_map_map (f := P) (g := R) (m := P.natDegree) (n := d) (Int.castRingHom ℂ)
  rw [eq_intCast] at h1
  rw [← h1, ← natDegree_toC P, resultant_eq_prod_eval (toC P) (toC R) d
    ((natDegree_toC R).le.trans hd) (IsAlgClosed.splits _), leadingCoeff_toC]

/-- **Resultant bound** (general form). If `P ≠ 0` and `R` vanishes at no complex root of `P`, then
`∑ log |R(αᵢ)| ≥ -d log |a|` for every `d ≥ deg R` (sum over the roots with multiplicity). -/
theorem neg_mul_log_le_sum_log_norm_eval {P : ℤ[X]} (hP0 : P ≠ 0) (R : ℤ[X]) (d : ℕ)
    (hd : R.natDegree ≤ d) (hR : ∀ β ∈ (toC P).roots, eval β (toC R) ≠ 0) :
    -((d : ℝ) * Real.log |(P.leadingCoeff : ℝ)|) ≤
      ((toC P).roots.map (fun β => Real.log ‖eval β (toC R)‖)).sum := by
  have hr := intCast_resultant P R d hd
  have ha : (P.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hP0
  have hprod : ((toC P).roots.map (fun β => eval β (toC R))).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    rw [Multiset.mem_map]
    rintro ⟨β, hβ, h0⟩
    exact hR β hβ h0
  have hr0 : P.resultant R P.natDegree d ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hr
    exact mul_ne_zero (pow_ne_zero _ ha) hprod hr.symm
  have h1 : (1 : ℝ) ≤ ‖((P.resultant R P.natDegree d : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hr0
  have h2 := Real.log_nonneg h1
  have hnz : ∀ x ∈ (toC P).roots.map (fun β => ‖eval β (toC R)‖), x ≠ 0 := by
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact norm_ne_zero_iff.mpr (hR β hβ)
  rw [hr, norm_mul, norm_pow, Multiset.norm_prod, Multiset.map_map] at h2
  simp only [Function.comp_def] at h2
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr ha)) (Multiset.prod_ne_zero (fun h => hnz 0 h rfl)),
    Real.log_pow, Real.log_multiset_prod hnz, Multiset.map_map] at h2
  simp only [Function.comp_def] at h2
  rw [Complex.norm_intCast] at h2
  linarith

end basic

namespace IsMinpolyZ

variable {P : ℤ[X]} {α : ℂ}

theorem ne_zero (hP : IsMinpolyZ P α) : P ≠ 0 := by
  rintro rfl
  exact (lt_irrefl 0) (by simpa using hP.2.1)

theorem irreducible_rat (hP : IsMinpolyZ P α) : Irreducible (P.map (Int.castRingHom ℚ)) := by
  have hprim := hP.1.isPrimitive hP.2.1.ne'
  rw [← algebraMap_int_eq]
  exact (hprim.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hP.1

theorem separable_toC (hP : IsMinpolyZ P α) : (toC P).Separable := by
  rw [toC_eq_map_rat]
  exact hP.irreducible_rat.separable.map

theorem nodup_roots (hP : IsMinpolyZ P α) : (toC P).roots.Nodup :=
  Polynomial.nodup_roots hP.separable_toC

theorem val_rootsC (hP : IsMinpolyZ P α) : (rootsC P).val = (toC P).roots := by
  rw [Multiset.toFinset_val]
  exact hP.nodup_roots.dedup

theorem card_rootsC (hP : IsMinpolyZ P α) : (rootsC P).card = P.natDegree := by
  rw [Multiset.toFinset_card_of_nodup hP.nodup_roots, card_roots_toC]

theorem mem_rootsC (hP : IsMinpolyZ P α) {β : ℂ} : β ∈ rootsC P ↔ aeval β P = 0 := by
  rw [Multiset.mem_toFinset, mem_roots (toC_ne_zero hP.ne_zero), IsRoot.def, eval_toC]

/-- A polynomial that does not vanish at `α` vanishes at no conjugate of `α`. -/
theorem eval_ne_zero_of_mem_roots (hP : IsMinpolyZ P α) {R : ℤ[X]} (hR : aeval α R ≠ 0) {β : ℂ}
    (hβ : β ∈ (toC P).roots) : eval β (toC R) ≠ 0 := by
  have hirr := hP.irreducible_rat
  have hndvd : ¬ P.map (Int.castRingHom ℚ) ∣ R.map (Int.castRingHom ℚ) := by
    rintro ⟨S, hS⟩
    apply hR
    have h := congrArg (aeval α) hS
    rw [map_mul, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_map_algebraMap, hP.2.2,
      zero_mul] at h
    exact h
  obtain ⟨u, v, huv⟩ := (hirr.coprime_iff_not_dvd).mpr hndvd
  have h := congrArg (aeval β) huv
  rw [map_add, map_mul, map_mul, map_one, ← algebraMap_int_eq, aeval_map_algebraMap,
    aeval_map_algebraMap] at h
  have hβ0 : aeval β P = 0 := (hP.mem_rootsC).mp (Multiset.mem_toFinset.mpr hβ)
  rw [eval_toC]
  intro h0
  rw [hβ0, h0, mul_zero, mul_zero, add_zero] at h
  exact zero_ne_one h

theorem eval_ne_zero_of_mem_rootsC (hP : IsMinpolyZ P α) {R : ℤ[X]} (hR : aeval α R ≠ 0) {β : ℂ}
    (hβ : β ∈ rootsC P) : eval β (toC R) ≠ 0 :=
  hP.eval_ne_zero_of_mem_roots hR (Multiset.mem_toFinset.mp hβ)

/-- If `R(α) = 0` then `P ∣ R` in `ℚ[X]`. -/
theorem map_rat_dvd_of_aeval_eq_zero (hP : IsMinpolyZ P α) {R : ℤ[X]} (hR : aeval α R = 0) :
    P.map (Int.castRingHom ℚ) ∣ R.map (Int.castRingHom ℚ) := by
  by_contra hndvd
  obtain ⟨u, v, huv⟩ := (hP.irreducible_rat.coprime_iff_not_dvd).mpr hndvd
  have h := congrArg (aeval α) huv
  rw [map_add, map_mul, map_mul, map_one, ← algebraMap_int_eq, aeval_map_algebraMap,
    aeval_map_algebraMap, hP.2.2, hR, mul_zero, mul_zero, add_zero] at h
  exact zero_ne_one h

/-- If `R ≠ 0` and `R(α) = 0` then `deg P ≤ deg R`. -/
theorem natDegree_le_of_aeval_eq_zero (hP : IsMinpolyZ P α) {R : ℤ[X]} (hR0 : R ≠ 0)
    (hR : aeval α R = 0) : P.natDegree ≤ R.natDegree := by
  have h := natDegree_le_of_dvd (hP.map_rat_dvd_of_aeval_eq_zero hR)
    ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr hR0)
  rwa [natDegree_map_eq_of_injective (RingHom.injective_int _),
    natDegree_map_eq_of_injective (RingHom.injective_int _)] at h

/-- **Resultant bound (A1).** `∑ᵢ log |R(αᵢ)| ≥ -(deg R) log |a|` for `R(α) ≠ 0`. -/
theorem sum_log_norm_eval_ge (hP : IsMinpolyZ P α) {R : ℤ[X]} (hR : aeval α R ≠ 0) :
    -((R.natDegree : ℝ) * Real.log |(P.leadingCoeff : ℝ)|) ≤
      ∑ β ∈ rootsC P, Real.log ‖eval β (toC R)‖ := by
  rw [Finset.sum_eq_multiset_sum, hP.val_rootsC]
  exact neg_mul_log_le_sum_log_norm_eval hP.ne_zero R R.natDegree le_rfl
    (fun β hβ => hP.eval_ne_zero_of_mem_roots hR hβ)

/-- `P'(β) = a ∏_{γ ≠ β} (β - γ)` at a root `β`. -/
theorem eval_derivative_toC [DecidableEq ℂ] {β : ℂ} (hβ : β ∈ (toC P).roots) :
    eval β (toC (derivative P)) =
      (P.leadingCoeff : ℂ) * (((toC P).roots.erase β).map (fun γ => β - γ)).prod := by
  have hs := IsAlgClosed.splits (toC P)
  have hd : toC (derivative P) = derivative (toC P) := (derivative_map P _).symm
  rw [hd]
  conv_lhs => rw [hs.eq_prod_roots]
  rw [derivative_C_mul, eval_C_mul, eval_multiset_prod_X_sub_C_derivative hβ, leadingCoeff_toC]

/-- **Discriminant bound (A2).** `∑_{i ≠ k} log |αᵢ - αₖ| ≥ -(2n - 2) log |a|`. -/
theorem sum_log_norm_sub_ge (hP : IsMinpolyZ P α) :
    -((2 * (P.natDegree : ℝ) - 2) * Real.log |(P.leadingCoeff : ℝ)|) ≤
      ∑ β ∈ rootsC P, ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖ := by
  classical
  have hP0 := hP.ne_zero
  have hn : 0 < P.natDegree := hP.2.1
  have ha : (P.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hP0
  have hres := intCast_resultant P (derivative P) (P.natDegree - 1) (natDegree_derivative_le P)
  have hdisc := resultant_deriv (f := P) (natDegree_pos_iff_degree_pos.mp hn)
  -- the product over the roots, as a finset product
  have hprod : ((toC P).roots.map (fun β => eval β (toC (derivative P)))).prod =
      ∏ β ∈ rootsC P, ((P.leadingCoeff : ℂ) * ∏ γ ∈ (rootsC P).erase β, (β - γ)) := by
    rw [Finset.prod_eq_multiset_prod, hP.val_rootsC]
    congr 1
    apply Multiset.map_congr rfl
    intro β hβ
    rw [eval_derivative_toC hβ, Finset.prod_eq_multiset_prod, Finset.erase_val, hP.val_rootsC]
  rw [hprod] at hres
  -- every factor is nonzero
  have hfac : ∀ β ∈ rootsC P, ((P.leadingCoeff : ℂ) * ∏ γ ∈ (rootsC P).erase β, (β - γ)) ≠ 0 := by
    intro β _
    refine mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr ?_)
    intro γ hγ
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hγ).symm
  have hRne : ((P.resultant (derivative P) P.natDegree (P.natDegree - 1) : ℤ) : ℂ) ≠ 0 := by
    rw [hres]
    exact mul_ne_zero (pow_ne_zero _ ha) (Finset.prod_ne_zero_iff.mpr hfac)
  -- the discriminant is a nonzero integer
  have hD0 : P.discr ≠ 0 := by
    intro h
    apply hRne
    rw [hdisc, h, mul_zero, Int.cast_zero]
  have hD1 : (1 : ℝ) ≤ |(P.discr : ℝ)| := by exact_mod_cast Int.one_le_abs hD0
  -- log of the norm of the resultant, two ways
  have hlog1 : Real.log ‖((P.resultant (derivative P) P.natDegree (P.natDegree - 1) : ℤ) : ℂ)‖ =
      Real.log |(P.leadingCoeff : ℝ)| + Real.log |(P.discr : ℝ)| := by
    rw [hdisc, Complex.norm_intCast, Int.cast_mul, Int.cast_mul, abs_mul, abs_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Real.log_mul (abs_ne_zero.mpr (by exact_mod_cast leadingCoeff_ne_zero.mpr hP0))
        (abs_ne_zero.mpr (by exact_mod_cast hD0))]
  have hlog2 : Real.log ‖((P.resultant (derivative P) P.natDegree (P.natDegree - 1) : ℤ) : ℂ)‖ =
      (2 * (P.natDegree : ℝ) - 1) * Real.log |(P.leadingCoeff : ℝ)| +
        ∑ β ∈ rootsC P, ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖ := by
    have hnorm_a : ‖(P.leadingCoeff : ℂ)‖ = |(P.leadingCoeff : ℝ)| := Complex.norm_intCast _
    have ha' : |(P.leadingCoeff : ℝ)| ≠ 0 := by rw [← hnorm_a]; exact norm_ne_zero_iff.mpr ha
    rw [hres, norm_mul, norm_pow, norm_prod, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
      (Finset.prod_ne_zero_iff.mpr (fun β hβ => norm_ne_zero_iff.mpr (hfac β hβ))),
      Real.log_pow, Real.log_prod (fun β hβ => norm_ne_zero_iff.mpr (hfac β hβ))]
    have hinner : ∀ β ∈ rootsC P, Real.log ‖(P.leadingCoeff : ℂ) * ∏ γ ∈ (rootsC P).erase β, (β - γ)‖ =
        Real.log |(P.leadingCoeff : ℝ)| + ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖ := by
      intro β _
      have hne : ∀ γ ∈ (rootsC P).erase β, ‖β - γ‖ ≠ 0 := fun γ hγ =>
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Finset.ne_of_mem_erase hγ).symm)
      rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr ha) (Finset.prod_ne_zero_iff.mpr hne),
        Real.log_prod hne, hnorm_a]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, Finset.sum_const, hP.card_rootsC,
      nsmul_eq_mul, hnorm_a, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne'), Nat.cast_one]
    ring
  have hlogD : 0 ≤ Real.log |(P.discr : ℝ)| := Real.log_nonneg hD1
  linarith

/-- **Discriminant bound (A2), weaker form.** `∑_{i ≠ k} log |αᵢ - αₖ| ≥ -(2n - 1) log |a|`. -/
theorem sum_log_norm_sub_ge' (hP : IsMinpolyZ P α) :
    -((2 * (P.natDegree : ℝ) - 1) * Real.log |(P.leadingCoeff : ℝ)|) ≤
      ∑ β ∈ rootsC P, ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖ := by
  have h := hP.sum_log_norm_sub_ge
  have ha : 0 ≤ Real.log |(P.leadingCoeff : ℝ)| := by
    apply Real.log_nonneg
    exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hP.ne_zero)
  nlinarith

end IsMinpolyZ

end AuxCommon
