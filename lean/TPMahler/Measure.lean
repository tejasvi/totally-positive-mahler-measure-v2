import TPMahler.Statement

/-!
# The reference measure `ν = ρ / s`

For nodes `e 0 < e 1 < ⋯ < e N` and values `G k ≥ 0` (`k ≤ N`), let `g = pwLin N e G` (the piecewise-linear
function with values `G k` at the nodes), `s = ∑_{k < N} (e (k+1) - e k) (G k + G (k+1)) / 2` and
`ν = s⁻¹ ρ`, where `ρ` is the push-forward of `g(y) dy` to `ℂ` (`nuPw`). Then:

* `integral_pwLin`: `∫ g = s`;
* `isProbabilityMeasure_nuPw`, `compactSupp_nuPw`;
* `discBound_nuPw`: `DiscBound ν (2 Gm / s)` for every `Gm ≥ max G` (a disc of radius `r` meets `ℝ` in an interval of
  length `≤ 2r`);
* `logPot_nuPw`: `U_ν(x) = s⁻¹ ∫ log |x - y| g(y) dy` for real `x`;
* `logEnergy_nuPw`: `I(ν) = s⁻² ∬ log |x - y| g(y) g(x) dy dx`;
* `logPot_nuPw_eq_closedForm`, `logEnergy_nuPw_eq_closedForm`: the same with the closed forms of `PwLinClosedForm`.
-/

open MeasureTheory Set Filter Topology
open AuxCommon

namespace TPMahler

/-! ## The pieces of `pwLin` -/

/-- The linear interpolant on `[e k, e (k+1)]`. -/
noncomputable def pwAff (e G : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (G k * (e (k + 1) - x) + G (k + 1) * (x - e k)) / (e (k + 1) - e k)

/-- The `k`-th summand of `pwLin`. -/
noncomputable def pwPiece (e G : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  if e k ≤ x ∧ x < e (k + 1) then (G k * (e (k + 1) - x) + G (k + 1) * (x - e k)) / (e (k + 1) - e k) else 0

theorem pwLin_eq_sum_pwPiece (N : ℕ) (e G : ℕ → ℝ) (x : ℝ) :
    pwLin N e G x = ∑ k ∈ Finset.range N, pwPiece e G k x := rfl

theorem pwPiece_eq_indicator (e G : ℕ → ℝ) (k : ℕ) :
    pwPiece e G k = Set.indicator (Set.Ico (e k) (e (k + 1))) (pwAff e G k) := by
  funext x
  unfold pwPiece pwAff
  by_cases h : e k ≤ x ∧ x < e (k + 1)
  · rw [ite_eq_left h, Set.indicator_of_mem (Set.mem_Ico.mpr h)]
  · rw [ite_eq_right h, Set.indicator_of_notMem (fun h' => h (Set.mem_Ico.mp h'))]

theorem continuous_pwAff (e G : ℕ → ℝ) (k : ℕ) : Continuous (pwAff e G k) := by
  unfold pwAff
  fun_prop

theorem measurable_pwLin (N : ℕ) (e G : ℕ → ℝ) : Measurable (pwLin N e G) := by
  have : pwLin N e G = fun x => ∑ k ∈ Finset.range N, pwPiece e G k x := rfl
  rw [this]
  refine Finset.measurable_sum _ (fun k _ => ?_)
  rw [pwPiece_eq_indicator]
  exact (continuous_pwAff e G k).measurable.indicator measurableSet_Ico

theorem integrable_pwPiece (e G : ℕ → ℝ) (k : ℕ) : Integrable (pwPiece e G k) := by
  rw [pwPiece_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (((continuous_pwAff e G k).integrableOn_Icc).mono_set Ico_subset_Icc_self)

theorem integrable_pwLin (N : ℕ) (e G : ℕ → ℝ) : Integrable (pwLin N e G) := by
  have : pwLin N e G = fun x => ∑ k ∈ Finset.range N, pwPiece e G k x := rfl
  rw [this]
  exact integrable_finsetSum _ (fun k _ => integrable_pwPiece e G k)

theorem integral_pwPiece (e G : ℕ → ℝ) (k : ℕ) (hk : e k < e (k + 1)) :
    ∫ x, pwPiece e G k x = (e (k + 1) - e k) * (G k + G (k + 1)) / 2 := by
  have hne : e (k + 1) - e k ≠ 0 := sub_ne_zero.mpr hk.ne'
  rw [pwPiece_eq_indicator, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hk.le]
  have h : ∀ x, pwAff e G k x = (G k * e (k + 1) - G (k + 1) * e k) / (e (k + 1) - e k) +
      (G (k + 1) - G k) / (e (k + 1) - e k) * x := by
    intro x
    unfold pwAff
    field_simp
    ring
  simp_rw [h]
  have hi1 : IntervalIntegrable (fun _ : ℝ => (G k * e (k + 1) - G (k + 1) * e k) / (e (k + 1) - e k))
      volume (e k) (e (k + 1)) := intervalIntegrable_const
  have hi2 : IntervalIntegrable (fun x : ℝ => (G (k + 1) - G k) / (e (k + 1) - e k) * x)
      volume (e k) (e (k + 1)) := (by fun_prop : Continuous fun x : ℝ =>
        (G (k + 1) - G k) / (e (k + 1) - e k) * x).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  field_simp
  ring

/-! ## Elementary properties of `pwLin` -/

section props

variable {N : ℕ} {e G : ℕ → ℝ}

/-- `∫ pwLin N e G = s` (trapezoid rule, exact for piecewise-linear functions). -/
theorem integral_pwLin (he : ∀ k < N, e k < e (k + 1)) :
    ∫ x, pwLin N e G x = ∑ k ∈ Finset.range N, (e (k + 1) - e k) * (G k + G (k + 1)) / 2 := by
  have : pwLin N e G = fun x => ∑ k ∈ Finset.range N, pwPiece e G k x := rfl
  rw [this, integral_finsetSum _ (fun k _ => integrable_pwPiece e G k)]
  exact Finset.sum_congr rfl (fun k hk => integral_pwPiece e G k (he k (Finset.mem_range.mp hk)))

theorem pwPiece_nonneg {k : ℕ} (hk0 : 0 ≤ G k) (hk1 : 0 ≤ G (k + 1)) (x : ℝ) : 0 ≤ pwPiece e G k x := by
  unfold pwPiece
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    apply div_nonneg
    · have := mul_nonneg hk0 (sub_nonneg.mpr h2.le)
      have := mul_nonneg hk1 (sub_nonneg.mpr h1)
      linarith
    · linarith
  · exact le_rfl

theorem pwLin_nonneg (hG : ∀ k ≤ N, 0 ≤ G k) (x : ℝ) : 0 ≤ pwLin N e G x := by
  rw [pwLin_eq_sum_pwPiece]
  refine Finset.sum_nonneg fun k hk => pwPiece_nonneg (hG k ?_) (hG (k + 1) ?_) x
  · exact (Finset.mem_range.mp hk).le
  · exact Finset.mem_range.mp hk

theorem nodes_mono (he : ∀ k < N, e k < e (k + 1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : e i ≤ e j := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (by omega) (by omega)).trans (he j (by omega)).le
    · obtain rfl : i = j + 1 := by omega
      exact le_rfl

theorem pwPiece_eq_zero_of_ne (he : ∀ k < N, e k < e (k + 1)) {k k' : ℕ} (hk : k < N) (hk' : k' < N)
    (hne : k ≠ k') {x : ℝ} (hx : e k ≤ x ∧ x < e (k + 1)) : pwPiece e G k' x = 0 := by
  unfold pwPiece
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := nodes_mono he (show k + 1 ≤ k' by omega) hk'.le
    linarith [hx.2]
  · have := nodes_mono he (show k' + 1 ≤ k by omega) hk.le
    linarith [hx.1]

/-- `pwLin N e G ≤ Gm` for every upper bound `Gm` of the node values. -/
theorem pwLin_le (he : ∀ k < N, e k < e (k + 1)) (hG : ∀ k ≤ N, 0 ≤ G k) {Gm : ℝ}
    (hGm : ∀ k ≤ N, G k ≤ Gm) (x : ℝ) : pwLin N e G x ≤ Gm := by
  have hGm0 : 0 ≤ Gm := (hG 0 (Nat.zero_le _)).trans (hGm 0 (Nat.zero_le _))
  by_cases hx : ∃ k < N, e k ≤ x ∧ x < e (k + 1)
  · obtain ⟨k, hk, hxk⟩ := hx
    rw [pwLin_eq_sum_pwPiece, Finset.sum_eq_single k]
    · unfold pwPiece
      rw [ite_eq_left hxk]
      have hpos : 0 < e (k + 1) - e k := by linarith [hxk.1, hxk.2]
      rw [div_le_iff₀ hpos]
      have h1 := mul_nonneg (sub_nonneg.mpr (hGm k hk.le)) (sub_nonneg.mpr hxk.2.le)
      have h2 := mul_nonneg (sub_nonneg.mpr (hGm (k + 1) hk)) (sub_nonneg.mpr hxk.1)
      nlinarith
    · intro k' hk' hne
      exact pwPiece_eq_zero_of_ne he hk (Finset.mem_range.mp hk') (Ne.symm hne) hxk
    · intro hk'
      exact absurd (Finset.mem_range.mpr hk) hk'
  · push Not at hx
    rw [pwLin_eq_sum_pwPiece, Finset.sum_eq_zero]
    · exact hGm0
    · intro k hk
      unfold pwPiece
      rw [ite_eq_right]
      rintro ⟨h1, h2⟩
      exact absurd h2 (not_lt.mpr (hx k (Finset.mem_range.mp hk) h1))

/-- `pwLin N e G` vanishes outside `[e 0, e N)`. -/
theorem pwLin_eq_zero_of_notMem (he : ∀ k < N, e k < e (k + 1)) {x : ℝ} (hx : x < e 0 ∨ e N ≤ x) :
    pwLin N e G x = 0 := by
  rw [pwLin_eq_sum_pwPiece]
  apply Finset.sum_eq_zero
  intro k hk
  have hk := Finset.mem_range.mp hk
  unfold pwPiece
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  have h0k := nodes_mono he (Nat.zero_le k) hk.le
  have hkN := nodes_mono he (show k + 1 ≤ N by omega) le_rfl
  rcases hx with hx | hx <;> linarith

end props

/-! ## The measures `ρ` and `ν = ρ / s` -/

/-- `ρ`: the push-forward to `ℂ` of the measure `pwLin N e G y dy` on `ℝ`. -/
noncomputable def rhoPw (N : ℕ) (e G : ℕ → ℝ) : Measure ℂ :=
  (volume.withDensity (fun y => ENNReal.ofReal (pwLin N e G y))).map (fun y : ℝ => (y : ℂ))

/-- The reference measure `ν = ρ / s`. -/
noncomputable def nuPw (N : ℕ) (e G : ℕ → ℝ) (s : ℝ) : Measure ℂ :=
  (ENNReal.ofReal s)⁻¹ • rhoPw N e G

theorem nuPw_def (N : ℕ) (e G : ℕ → ℝ) (s : ℝ) :
    nuPw N e G s = (ENNReal.ofReal s)⁻¹ •
      ((volume.withDensity (fun y => ENNReal.ofReal (pwLin N e G y))).map (fun y : ℝ => (y : ℂ))) := rfl

theorem measurableEmbedding_ofReal : MeasurableEmbedding (fun y : ℝ => (y : ℂ)) :=
  Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding

section measure

variable {N : ℕ} {e G : ℕ → ℝ}

theorem rhoPw_apply {A : Set ℂ} (hA : MeasurableSet A) :
    rhoPw N e G A = ∫⁻ y in (fun y : ℝ => (y : ℂ)) ⁻¹' A, ENNReal.ofReal (pwLin N e G y) := by
  rw [rhoPw, Measure.map_apply Complex.measurable_ofReal hA,
    withDensity_apply _ (Complex.measurable_ofReal hA)]

theorem rhoPw_univ (he : ∀ k < N, e k < e (k + 1)) (hG : ∀ k ≤ N, 0 ≤ G k) :
    rhoPw N e G univ =
      ENNReal.ofReal (∑ k ∈ Finset.range N, (e (k + 1) - e k) * (G k + G (k + 1)) / 2) := by
  rw [rhoPw_apply MeasurableSet.univ, preimage_univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_pwLin N e G) (ae_of_all _ (pwLin_nonneg hG)),
    integral_pwLin he]

/-- `ν` is a probability measure. -/
theorem isProbabilityMeasure_nuPw (he : ∀ k < N, e k < e (k + 1)) (hG : ∀ k ≤ N, 0 ≤ G k) {s : ℝ}
    (hs : ∑ k ∈ Finset.range N, (e (k + 1) - e k) * (G k + G (k + 1)) / 2 = s) (hs0 : 0 < s) :
    IsProbabilityMeasure (nuPw N e G s) := by
  constructor
  rw [nuPw, Measure.smul_apply, rhoPw_univ he hG, hs, smul_eq_mul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hs0).ne' ENNReal.ofReal_ne_top]

/-- `ν` has compact support (in the closed disc of radius `max |e 0| |e N|`). -/
theorem compactSupp_nuPw (he : ∀ k < N, e k < e (k + 1)) (s : ℝ) : CompactSupp (nuPw N e G s) := by
  refine ⟨max |e 0| |e N|, ?_⟩
  rw [nuPw, Measure.smul_apply, rhoPw_apply measurableSet_closedBall.compl, smul_eq_mul,
    setLIntegral_eq_zero (Complex.measurable_ofReal measurableSet_closedBall.compl), mul_zero]
  intro y hy
  simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
    Real.norm_eq_abs, not_le] at hy
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
  rw [pwLin_eq_zero_of_notMem he]
  by_contra h
  push Not at h
  have hy' : |y| ≤ max |e 0| |e N| := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (e 0)
      have := le_max_left |e 0| |e N|
      linarith [h.1]
    · have := le_abs_self (e N)
      have := le_max_right |e 0| |e N|
      linarith [h.2]
  linarith

/-- **Disc bound.** `ν(D(y, r)) ≤ (2 Gm / s) r` for every upper bound `Gm` of the node values. -/
theorem discBound_nuPw (he : ∀ k < N, e k < e (k + 1)) (hG : ∀ k ≤ N, 0 ≤ G k) {Gm : ℝ}
    (hGm : ∀ k ≤ N, G k ≤ Gm) {s : ℝ} (hs0 : 0 < s) : DiscBound (nuPw N e G s) (2 * Gm / s) := by
  intro y r hr _
  have hGm0 : 0 ≤ Gm := (hG 0 (Nat.zero_le _)).trans (hGm 0 (Nat.zero_le _))
  have hsub : (fun x : ℝ => (x : ℂ)) ⁻¹' Metric.ball y r ⊆ Ioo (y.re - r) (y.re + r) := by
    intro x hx
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm] at hx
    have h1 := Complex.abs_re_le_norm ((x : ℂ) - y)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hx)
    exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
  have hle : nuPw N e G s (Metric.ball y r) ≤
      (ENNReal.ofReal s)⁻¹ * (ENNReal.ofReal Gm * ENNReal.ofReal (2 * r)) := by
    rw [nuPw, Measure.smul_apply, rhoPw_apply measurableSet_ball, smul_eq_mul]
    gcongr
    calc ∫⁻ x in (fun x : ℝ => (x : ℂ)) ⁻¹' Metric.ball y r, ENNReal.ofReal (pwLin N e G x)
        ≤ ∫⁻ x in (fun x : ℝ => (x : ℂ)) ⁻¹' Metric.ball y r, ENNReal.ofReal Gm :=
          setLIntegral_mono measurable_const
            (fun x _ => ENNReal.ofReal_le_ofReal (pwLin_le he hG hGm x))
      _ = ENNReal.ofReal Gm * volume ((fun x : ℝ => (x : ℂ)) ⁻¹' Metric.ball y r) :=
          setLIntegral_const _ _
      _ ≤ ENNReal.ofReal Gm * volume (Ioo (y.re - r) (y.re + r)) := by
          gcongr
      _ = ENNReal.ofReal Gm * ENNReal.ofReal (2 * r) := by
          rw [Real.volume_Ioo]
          congr 2
          ring
  have hfin : (ENNReal.ofReal s)⁻¹ * (ENNReal.ofReal Gm * ENNReal.ofReal (2 * r)) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hs0).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  calc (nuPw N e G s (Metric.ball y r)).toReal
      ≤ ((ENNReal.ofReal s)⁻¹ * (ENNReal.ofReal Gm * ENNReal.ofReal (2 * r))).toReal :=
        ENNReal.toReal_mono hfin hle
    _ = s⁻¹ * (Gm * (2 * r)) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hs0.le,
          ENNReal.toReal_ofReal hGm0, ENNReal.toReal_ofReal (by linarith)]
    _ = 2 * Gm / s * r := by
        field_simp

/-- Integrals against `ν`: `∫ f dν = s⁻¹ ∫ g(x) f(x) dx` for every `f : ℂ → ℝ`. -/
theorem integral_nuPw (hG : ∀ k ≤ N, 0 ≤ G k) {s : ℝ} (hs0 : 0 < s) (f : ℂ → ℝ) :
    ∫ z, f z ∂(nuPw N e G s) = (1 / s) * ∫ x, pwLin N e G x * f x := by
  rw [nuPw, integral_smul_measure, rhoPw, measurableEmbedding_ofReal.integral_map,
    integral_withDensity_eq_integral_toReal_smul (measurable_pwLin N e G).ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hs0.le, smul_eq_mul, one_div]
  congr 1
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (pwLin_nonneg hG x)]

/-- **Potential of `ν`** at real points. -/
theorem logPot_nuPw (hG : ∀ k ≤ N, 0 ≤ G k) {s : ℝ} (hs0 : 0 < s) (x : ℝ) :
    logPot (nuPw N e G s) x = (1 / s) * ∫ y, Real.log |x - y| * pwLin N e G y := by
  rw [logPot, integral_nuPw hG hs0]
  congr 1
  congr 1
  funext y
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- **Energy of `ν`.** -/
theorem logEnergy_nuPw (hG : ∀ k ≤ N, 0 ≤ G k) {s : ℝ} (hs0 : 0 < s) :
    logEnergy (nuPw N e G s) =
      (1 / s ^ 2) * ∫ x, ∫ y, Real.log |x - y| * pwLin N e G y * pwLin N e G x := by
  rw [logEnergy, integral_nuPw hG hs0]
  have h1 : ∀ x : ℝ, pwLin N e G x * logPot (nuPw N e G s) x =
      (1 / s) * ∫ y, Real.log |x - y| * pwLin N e G y * pwLin N e G x := by
    intro x
    rw [logPot_nuPw hG hs0, integral_mul_const]
    ring
  rw [integral_congr_ae (ae_of_all _ h1), integral_const_mul]
  ring

/-- `U_ν(x)` in closed form (Lemma 3.1 of the paper, assumed as `PwLinClosedForm`). -/
theorem logPot_nuPw_eq_closedForm (hC : PwLinClosedForm) (he : ∀ k < N, e k < e (k + 1))
    (hG : ∀ k ≤ N, 0 ≤ G k) (hG0 : G 0 = 0) (hGN : G N = 0) {s : ℝ} (hs0 : 0 < s) (x : ℝ) :
    logPot (nuPw N e G s) x =
      (1 / s) * ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x) := by
  rw [logPot_nuPw hG hs0, (hC N e G he hG0 hGN).1 x]

/-- `I(ν)` in closed form (Lemma 3.1 of the paper, assumed as `PwLinClosedForm`). -/
theorem logEnergy_nuPw_eq_closedForm (hC : PwLinClosedForm) (he : ∀ k < N, e k < e (k + 1))
    (hG : ∀ k ≤ N, 0 ≤ G k) (hG0 : G 0 = 0) (hGN : G N = 0) {s : ℝ} (hs0 : 0 < s) :
    logEnergy (nuPw N e G s) =
      (1 / s ^ 2) * ∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
        slopeJump N e G i * slopeJump N e G k * Lk (e i - e k) := by
  rw [logEnergy_nuPw hG hs0, (hC N e G he hG0 hGN).2]

end measure

end TPMahler
