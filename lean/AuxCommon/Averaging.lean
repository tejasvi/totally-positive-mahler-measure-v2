import AuxCommon.Resultant

/-!
# Steps of Lemma 2.2 shared by both papers

* `log_mahlerMeasure_toC`, `IsMinpolyZ.log_mahlerMeasure_eq`: `log M(P) = log |a| + ∑ᵢ log⁺ |αᵢ|`.
* `IsMinpolyZ.energy_sum_ge`: `∑ᵢ (2 U_ν(αᵢ) - I(ν)) ≥ -2 log |a| - log (2Kn) - 1` for `n = deg P ≥ 1/(2K)`: the named
  hypothesis `EnergySmoothing` with `r = 1/(2Kn)` and the discriminant bound `IsMinpolyZ.sum_log_norm_sub_ge`.
-/

open Polynomial MeasureTheory

namespace AuxCommon

/-- `log M(P) = log |a| + ∑ log⁺ |αᵢ|` (roots with multiplicity). -/
theorem log_mahlerMeasure_toC (P : ℤ[X]) :
    Real.log (toC P).mahlerMeasure =
      Real.log |(P.leadingCoeff : ℝ)| + ((toC P).roots.map (fun β => Real.posLog ‖β‖)).sum := by
  rw [← logMahlerMeasure_eq_log_MahlerMeasure, logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots,
    leadingCoeff_toC, Complex.norm_intCast]

namespace IsMinpolyZ

variable {P : ℤ[X]} {α : ℂ}

/-- `log M(P) = log |a| + ∑ᵢ log⁺ |αᵢ|` over the (distinct) roots of a minimal polynomial. -/
theorem log_mahlerMeasure_eq (hP : IsMinpolyZ P α) :
    Real.log (toC P).mahlerMeasure =
      Real.log |(P.leadingCoeff : ℝ)| + ∑ β ∈ rootsC P, Real.posLog ‖β‖ := by
  rw [log_mahlerMeasure_toC, ← hP.val_rootsC, ← Finset.sum_eq_multiset_sum]

theorem log_abs_leadingCoeff_nonneg (hP : IsMinpolyZ P α) : 0 ≤ Real.log |(P.leadingCoeff : ℝ)| :=
  Real.log_nonneg (by exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hP.ne_zero))

/-- **Energy at the conjugates.** `EnergySmoothing` with `r = 1/(2Kn)` and the discriminant bound give
`∑ᵢ (2 U_ν(αᵢ) - I(ν)) ≥ -2 log |a| - log (2Kn) - 1` (paper (2.9) times `n`, with `2n - 2 ≤ 2n`). -/
theorem energy_sum_ge (hE : EnergySmoothing) (ν : Measure ℂ) [IsProbabilityMeasure ν] {K : ℝ}
    (hK : 0 < K) (hsupp : CompactSupp ν) (hdisc : DiscBound ν K) (hP : IsMinpolyZ P α)
    (hn : 1 / (2 * K) ≤ P.natDegree) :
    -2 * Real.log |(P.leadingCoeff : ℝ)| - Real.log (2 * K * P.natDegree) - 1 ≤
      ∑ β ∈ rootsC P, (2 * logPot ν β - logEnergy ν) := by
  classical
  have hn0 : 0 < P.natDegree := hP.2.1
  have hnR : (0 : ℝ) < P.natDegree := by exact_mod_cast hn0
  have hcard : (rootsC P).card = P.natDegree := hP.card_rootsC
  have hLa := hP.log_abs_leadingCoeff_nonneg
  -- an enumeration of the roots
  let e : Fin P.natDegree ≃ rootsC P := ((rootsC P).equivFinOfCardEq hcard).symm
  let αf : Fin P.natDegree → ℂ := fun i => (e i : ℂ)
  have hinj : Function.Injective αf := fun i k h => e.injective (Subtype.ext h)
  have hsumE : ∀ f : ℂ → ℝ, ∑ i, f (αf i) = ∑ β ∈ rootsC P, f β := by
    intro f
    rw [← Finset.sum_coe_sort (rootsC P) f]
    exact e.sum_comp (fun x : rootsC P => f x)
  have hD : ∑ i, ∑ k ∈ Finset.univ.erase i, Real.log ‖αf i - αf k‖ =
      ∑ β ∈ rootsC P, ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖ := by
    have h1 : ∀ i, ∑ k ∈ Finset.univ.erase i, Real.log ‖αf i - αf k‖ =
        ∑ γ ∈ (rootsC P).erase (αf i), Real.log ‖αf i - γ‖ := by
      intro i
      rw [Finset.sum_erase _ (by simp), Finset.sum_erase _ (by simp),
        hsumE (fun γ => Real.log ‖αf i - γ‖)]
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]
    exact hsumE (fun β => ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖)
  -- smoothing radius r = 1/(2Kn)
  set r : ℝ := 1 / (2 * K * P.natDegree) with hr_def
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by
    rw [hr_def, div_le_one (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hn
    linarith
  have hES := hE ν inferInstance K hK hsupp hdisc P.natDegree αf hn0 hinj r hr0 hr1
  rw [hD, hsumE (fun β => 2 * logPot ν β - logEnergy ν)] at hES
  have hlogr : Real.log r = -Real.log (2 * K * P.natDegree) := by
    rw [hr_def, one_div, Real.log_inv]
  have h2Kr : 2 * K * r = 1 / P.natDegree := by
    rw [hr_def]
    field_simp
  rw [hlogr, h2Kr] at hES
  have hDisc := hP.sum_log_norm_sub_ge
  set D := ∑ β ∈ rootsC P, ∑ γ ∈ (rootsC P).erase β, Real.log ‖β - γ‖
  set E := ∑ β ∈ rootsC P, (2 * logPot ν β - logEnergy ν)
  set La := Real.log |(P.leadingCoeff : ℝ)|
  set L2 := Real.log (2 * K * P.natDegree)
  set nR : ℝ := (P.natDegree : ℝ)
  have hDb : -(2 * nR * La) ≤ D := by nlinarith
  have h3 : 1 / nR ^ 2 * (-(2 * nR * La)) ≤ 1 / nR ^ 2 * D :=
    mul_le_mul_of_nonneg_left hDb (by positivity)
  have h4 : 1 / nR ^ 2 * (-(2 * nR * La)) = -2 * La / nR := by
    field_simp
  have h5 : (-2 * La - L2 - 1) / nR ≤ E / nR := by
    calc (-2 * La - L2 - 1) / nR = -2 * La / nR + -L2 / nR - 1 / nR := by ring
      _ ≤ 1 / nR ^ 2 * D + -L2 / nR - 1 / nR := by linarith
      _ ≤ 1 / nR * E := hES
      _ = E / nR := by ring
  exact (div_le_div_iff_of_pos_right hnR).mp h5

end IsMinpolyZ

end AuxCommon
