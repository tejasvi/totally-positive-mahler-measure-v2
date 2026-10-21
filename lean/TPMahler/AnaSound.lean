import TPMahler.PolySound
import TPMahler.ClosedForm

/-!
# Analytic lemmas for the soundness of the checker

* `chord_lower`: the chord bound (lem:chord in the form used by `chordLB`): if `f'' ≤ M` on `(p, q)`, then
  `f(x) ≥ chord(x) - max(M, 0) (q - p)² / 8` on `[p, q]`;
* `tangent_lower`: a convex function lies above its tangent at a point of differentiability;
* `hasDerivAt_Hk_all`, `hasDerivAt_Hd_abs`, `Hk_nonpos`, `abs_Hd_le`: calculus of `H(t) = t²/2 log|t| - 3t²/4`
  (`H'(t) = t log|t| - t` everywhere, `|H'| ≤ 47` on `[-22, 22]`);
* `posLog_*`: `log⁺` on `[0, 1]` and on `[1, ∞)`, its derivatives, and `posLog_chord_data` for a chord interval
  that does not contain `1` in its interior (the derivatives of `log |P|` are in `TPMahler.PolySound`);
* `hasDerivAt_sum_Hk`, `hasDerivAt_sum_Hd`: first and second derivatives of partial sums `∑_{i ∈ s} Cᵢ H(eᵢ - x)`;
* `Hk_sub_le`, `sum_Hk_lipschitz`, `UR_lipschitz`: the Lipschitz bound of `U` used by the windows and the left tail.
-/

open Polynomial Set

namespace TPMahler.Cert

/-! ## The chord lemma -/

/-- **Chord lemma.** If `f` is continuous on `[p, q]`, twice differentiable on `(p, q)` with `f'' ≤ M` there, then
`f(x) ≥ ((q - x) f(p) + (x - p) f(q)) / (q - p) - max(M, 0) (q - p)² / 8` for `x ∈ [p, q]`. -/
theorem chord_lower {f f' f'' : ℝ → ℝ} {p q M : ℝ} (hpq : p < q) (hf : ContinuousOn f (Icc p q))
    (hf' : ∀ x ∈ Ioo p q, HasDerivAt f (f' x) x) (hf'' : ∀ x ∈ Ioo p q, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Ioo p q, f'' x ≤ M) :
    ∀ x ∈ Icc p q, ((q - x) * f p + (x - p) * f q) / (q - p) - max M 0 * (q - p) ^ 2 / 8 ≤ f x := by
  set g : ℝ → ℝ := fun x => f x - M * ((x - p) * (x - q)) / 2 with hg
  have hint : interior (Icc p q) = Ioo p q := interior_Icc
  have hconc : ConcaveOn ℝ (Icc p q) g := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc p q)
      (f' := fun x => f' x - M * (2 * x - p - q) / 2) (f'' := fun x => f'' x - M) ?_ ?_ ?_ ?_
    · exact hf.sub (by fun_prop)
    · intro x hx
      rw [hint] at hx
      have h2 : HasDerivAt (fun x => M * ((x - p) * (x - q)) / 2) (M * (2 * x - p - q) / 2) x := by
        have := ((((hasDerivAt_id' x).sub_const p).mul ((hasDerivAt_id' x).sub_const q)).const_mul M).div_const 2
        convert this using 1
        ring
      exact ((hf' x hx).sub h2).hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have h2 : HasDerivAt (fun x => M * (2 * x - p - q) / 2) M x := by
        have := (((((hasDerivAt_id' x).const_mul 2).sub_const p).sub_const q).const_mul M).div_const 2
        convert this using 1
        ring
      exact ((hf'' x hx).sub h2).hasDerivWithinAt
    · intro x hx
      rw [hint] at hx
      have := hM x hx
      show f'' x - M ≤ 0
      linarith
  intro x hx
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have ha : 0 ≤ (q - x) / (q - p) := div_nonneg (by linarith [hx.2]) hqp.le
  have hb : 0 ≤ (x - p) / (q - p) := div_nonneg (by linarith [hx.1]) hqp.le
  have hab : (q - x) / (q - p) + (x - p) / (q - p) = 1 := by
    field_simp
    ring
  have h := hconc.2 (⟨le_rfl, hpq.le⟩ : p ∈ Icc p q) (⟨hpq.le, le_rfl⟩ : q ∈ Icc p q) ha hb hab
  have hx' : ((q - x) / (q - p)) • p + ((x - p) / (q - p)) • q = x := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hx'] at h
  simp only [smul_eq_mul, hg, sub_self, zero_mul, mul_zero, zero_div, sub_zero] at h
  have hchord : ((q - x) * f p + (x - p) * f q) / (q - p) =
      (q - x) / (q - p) * f p + (x - p) / (q - p) * f q := by
    field_simp
  have hbound : -(max M 0 * (q - p) ^ 2 / 8) ≤ M * ((x - p) * (x - q)) / 2 := by
    have ht0 : 0 ≤ (x - p) * (q - x) := mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
    have ht1 : (x - p) * (q - x) ≤ (q - p) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * x - p - q)]
    have hm0 : 0 ≤ max M 0 := le_max_right _ _
    have hmM : M ≤ max M 0 := le_max_left _ _
    nlinarith [mul_le_mul_of_nonneg_left ht1 hm0, mul_le_mul_of_nonneg_right hmM ht0]
  rw [hchord]
  linarith

/-! ## The tangent lemma -/

/-- **Tangent lemma.** A function convex on `[p, q]` and differentiable at `x₀ ∈ [p, q]` lies above its tangent. -/
theorem tangent_lower {g : ℝ → ℝ} {p q x0 d : ℝ} (hg : ConvexOn ℝ (Icc p q) g) (hx0 : x0 ∈ Icc p q)
    (hd : HasDerivAt g d x0) : ∀ x ∈ Icc p q, g x0 + d * (x - x0) ≤ g x := by
  intro x hx
  rcases lt_trichotomy x x0 with hlt | heq | hgt
  · have h := hg.slope_le_of_hasDerivAt hx hx0 hlt hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hlt)] at h
    linarith
  · rw [heq]
    simp
  · have h := hg.le_slope_of_hasDerivAt hx0 hx hgt hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hgt)] at h
    linarith

/-- The tangent lemma at an end point `x₀ ∈ {p, q}`. -/
theorem tangent_lower_end {g : ℝ → ℝ} {p q x0 d : ℝ} (hpq : p ≤ q) (hg : ConvexOn ℝ (Icc p q) g)
    (hx0 : x0 = p ∨ x0 = q) (hd : HasDerivAt g d x0) : ∀ x ∈ Icc p q, g x0 + d * (x - x0) ≤ g x := by
  refine tangent_lower hg ?_ hd
  rcases hx0 with rfl | rfl
  · exact ⟨le_rfl, hpq⟩
  · exact ⟨hpq, le_rfl⟩

/-! ## The kernel `H` -/

theorem Hd_abs_eq : (fun t : ℝ => t * Real.log |t| - t) = Hd := by
  funext t
  simp [Hd, Real.log_abs]

/-- `H'(t) = t log |t| - t` for every `t`, including `t = 0`. -/
theorem hasDerivAt_Hk_all (t : ℝ) : HasDerivAt Hk (t * Real.log |t| - t) t := by
  have hg : Continuous (fun t : ℝ => t * Real.log |t| - t) := by
    rw [Hd_abs_eq]
    exact continuous_Hd
  refine hasDerivAt_of_hasDerivAt_of_ne' (x := 0) (g := fun t : ℝ => t * Real.log |t| - t)
    (fun y hy => ?_) continuous_Hk.continuousAt hg.continuousAt t
  have e : y * Real.log |y| - y = Hd y := by simp [Hd, Real.log_abs]
  rw [e]
  exact hasDerivAt_Hk hy

/-- `H''(t) = log |t|` for `t ≠ 0`. -/
theorem hasDerivAt_Hd_abs {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => t * Real.log |t| - t) (Real.log |t|) t := by
  rw [Hd_abs_eq, Real.log_abs]
  exact hasDerivAt_Hd ht

/-- `H(t) ≤ 0` for `|t| ≤ 1`. -/
theorem Hk_nonpos {t : ℝ} (ht : |t| ≤ 1) : Hk t ≤ 0 := by
  unfold Hk
  have hl : Real.log |t| ≤ 0 := Real.log_nonpos (abs_nonneg t) ht
  have h1 : t ^ 2 / 2 * Real.log |t| ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hl
  nlinarith [sq_nonneg t]

theorem log_22_lt : Real.log 22 < 69 / 22 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : Real.exp (69 / 22) = Real.exp 1 ^ 3 * Real.exp (3 / 22) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [h1]
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by gcongr
  have h4 : (3 / 22 : ℝ) + 1 ≤ Real.exp (3 / 22) := Real.add_one_le_exp _
  calc (22 : ℝ) < (2.7182818283 : ℝ) ^ 3 * (3 / 22 + 1) := by norm_num
    _ ≤ Real.exp 1 ^ 3 * Real.exp (3 / 22) := by gcongr

/-- `|H'(t)| = |t log |t| - t| ≤ 47` for `|t| ≤ 22`. -/
theorem abs_Hd_le {t : ℝ} (ht : |t| ≤ 22) : |t * Real.log |t| - t| ≤ 47 := by
  have hfac : t * Real.log |t| - t = t * (Real.log |t| - 1) := by ring
  rw [hfac, abs_mul]
  set s := |t| with hs
  have hs0 : 0 ≤ s := abs_nonneg t
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp
  · rcases le_or_gt (Real.log s) 1 with hl | hl
    · rw [abs_of_nonpos (by linarith)]
      have h1 := Real.one_sub_inv_le_log_of_pos hpos
      have h2 : s - 1 ≤ s * Real.log s := by
        have := mul_le_mul_of_nonneg_left h1 hpos.le
        rw [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne'] at this
        exact this
      nlinarith
    · rw [abs_of_pos (by linarith)]
      have h22 : Real.log s ≤ Real.log 22 := Real.log_le_log hpos ht
      have := log_22_lt
      have hb : Real.log s - 1 ≤ 47 / 22 := by linarith
      calc s * (Real.log s - 1) ≤ 22 * (47 / 22) := mul_le_mul ht hb (by linarith) (by norm_num)
        _ = 47 := by norm_num

/-! ## `log⁺` -/

theorem posLog_eq_zero_of_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.posLog x = 0 :=
  (Real.posLog_eq_zero_iff x).mpr (by rw [abs_of_nonneg h0]; exact h1)

theorem posLog_eq_log_of_one_le {x : ℝ} (h : 1 ≤ x) : Real.posLog x = Real.log x :=
  Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith)]; exact h)

theorem hasDerivAt_posLog_of_one_lt {x : ℝ} (hx : 1 < x) : HasDerivAt Real.posLog x⁻¹ x := by
  have h := Real.hasDerivAt_log (by linarith : x ≠ 0)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact posLog_eq_log_of_one_le hy.le

theorem hasDerivAt_posLog_of_lt_one {x : ℝ} (h0 : 0 < x) (hx : x < 1) : HasDerivAt Real.posLog 0 x := by
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds h0, eventually_lt_nhds hx] with y hy0 hy1
  exact posLog_eq_zero_of_le_one hy0.le hy1.le

/-- `log⁺` on a chord interval `(p, q)` with `0 ≤ p` that does not contain `1` in its interior: twice
differentiable with second derivative `≤ 0`. -/
theorem posLog_chord_data {p q : ℝ} (hp : 0 ≤ p) (h1 : ¬ (p < 1 ∧ 1 < q)) :
    ∃ f' f'' : ℝ → ℝ, ∀ x ∈ Ioo p q,
      HasDerivAt Real.posLog (f' x) x ∧ HasDerivAt f' (f'' x) x ∧ f'' x ≤ 0 := by
  by_cases hq : q ≤ 1
  · refine ⟨fun _ => 0, fun _ => 0, fun x hx => ⟨?_, hasDerivAt_const x 0, le_rfl⟩⟩
    exact hasDerivAt_posLog_of_lt_one (lt_of_le_of_lt hp hx.1) (lt_of_lt_of_le hx.2 hq)
  · have hp1 : 1 ≤ p := by
      by_contra h
      push Not at h hq
      exact h1 ⟨h, hq⟩
    refine ⟨fun x => x⁻¹, fun x => -(x ^ 2)⁻¹, fun x hx => ⟨?_, ?_, ?_⟩⟩
    · exact hasDerivAt_posLog_of_one_lt (lt_of_le_of_lt hp1 hx.1)
    · exact hasDerivAt_inv (by linarith [hx.1] : x ≠ 0)
    · have : 0 ≤ (x ^ 2)⁻¹ := by positivity
      simp only
      linarith

/-- `log⁺` is monotone on `[0, ∞)`. -/
theorem posLog_le_posLog {u x : ℝ} (hu : 0 ≤ u) (hux : u ≤ x) : Real.posLog u ≤ Real.posLog x :=
  Real.monotoneOn_posLog (show (-1 : ℝ) ≤ u by linarith) (show (-1 : ℝ) ≤ x by linarith) hux

/-! ## Derivatives of partial sums of the potential -/

/-- `d/dx ∑_{i ∈ s} Cᵢ H(eᵢ - x) = -∑_{i ∈ s} Cᵢ H'(eᵢ - x)`, `H'(t) = t log |t| - t` (every `x`). -/
theorem hasDerivAt_sum_Hk (s : Finset ℕ) (C e : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (fun y => ∑ i ∈ s, C i * Hk (e i - y))
      (∑ i ∈ s, -(C i * ((e i - x) * Real.log |e i - x| - (e i - x)))) x := by
  have h : ∀ i ∈ s, HasDerivAt (fun y => C i * Hk (e i - y))
      (-(C i * ((e i - x) * Real.log |e i - x| - (e i - x)))) x := by
    intro i _
    have h1 : HasDerivAt (fun y => Hk (e i - y)) (((e i - x) * Real.log |e i - x| - (e i - x)) * (-1)) x :=
      (hasDerivAt_Hk_all (e i - x)).comp x ((hasDerivAt_id' x).const_sub (e i))
    refine (h1.const_mul (C i)).congr_deriv ?_
    ring
  have := HasDerivAt.fun_sum h
  convert this using 1

/-- `d/dx (-∑_{i ∈ s} Cᵢ H'(eᵢ - x)) = ∑_{i ∈ s} Cᵢ log |eᵢ - x|` at `x` different from the `eᵢ`, `i ∈ s`. -/
theorem hasDerivAt_sum_Hd (s : Finset ℕ) (C e : ℕ → ℝ) {x : ℝ} (hx : ∀ i ∈ s, e i ≠ x) :
    HasDerivAt (fun y => ∑ i ∈ s, -(C i * ((e i - y) * Real.log |e i - y| - (e i - y))))
      (∑ i ∈ s, C i * Real.log |e i - x|) x := by
  have h : ∀ i ∈ s, HasDerivAt (fun y => -(C i * ((e i - y) * Real.log |e i - y| - (e i - y))))
      (C i * Real.log |e i - x|) x := by
    intro i hi
    have hne : e i - x ≠ 0 := sub_ne_zero.mpr (hx i hi)
    have h1 : HasDerivAt (fun y => (e i - y) * Real.log |e i - y| - (e i - y)) (Real.log |e i - x| * (-1)) x :=
      (hasDerivAt_Hd_abs hne).comp x ((hasDerivAt_id' x).const_sub (e i))
    refine ((h1.const_mul (C i)).neg).congr_deriv ?_
    ring
  have := HasDerivAt.fun_sum h
  convert this using 1

/-! ## The Lipschitz bound of `U` -/

/-- `|H(a) - H(b)| ≤ 47 |a - b|` for `|a|, |b| ≤ 22`. -/
theorem Hk_sub_le {a b : ℝ} (ha : |a| ≤ 22) (hb : |b| ≤ 22) : |Hk a - Hk b| ≤ 47 * |a - b| := by
  have hs : Convex ℝ (Icc (-22 : ℝ) 22) := convex_Icc _ _
  have hd : ∀ t ∈ Icc (-22 : ℝ) 22, HasDerivWithinAt Hk (t * Real.log |t| - t) (Icc (-22) 22) t :=
    fun t _ => (hasDerivAt_Hk_all t).hasDerivWithinAt
  have hbd : ∀ t ∈ Icc (-22 : ℝ) 22, ‖t * Real.log |t| - t‖ ≤ 47 := fun t ht => by
    rw [Real.norm_eq_abs]
    exact abs_Hd_le (abs_le.mpr ht)
  have := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbd (abs_le.mp hb) (abs_le.mp ha)
  simpa [Real.norm_eq_abs] using this

/-- Lipschitz bound of `∑ Cᵢ H(eᵢ - x)` when all `|eᵢ - x| ≤ 22`. -/
theorem sum_Hk_lipschitz (N : ℕ) (e C : ℕ → ℝ) {y z : ℝ} (hy : ∀ i ≤ N, |e i - y| ≤ 22)
    (hz : ∀ i ≤ N, |e i - z| ≤ 22) :
    |∑ i ∈ Finset.range (N + 1), C i * Hk (e i - y) - ∑ i ∈ Finset.range (N + 1), C i * Hk (e i - z)| ≤
      47 * (∑ i ∈ Finset.range (N + 1), |C i|) * |y - z| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← mul_sub, abs_mul]
  have h := Hk_sub_le (hy i hi') (hz i hi')
  have e1 : (e i - y) - (e i - z) = -(y - z) := by ring
  rw [e1, abs_neg] at h
  calc |C i| * |Hk (e i - y) - Hk (e i - z)| ≤ |C i| * (47 * |y - z|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 47 * |C i| * |y - z| := by ring

/-- **Lipschitz bound of `U`** (certificate form). -/
theorem UR_lipschitz {y z : ℝ} (hy : ∀ i ≤ NN, |eR i - y| ≤ 22) (hz : ∀ i ≤ NN, |eR i - z| ≤ 22) :
    |UR y - UR z| ≤ 47 * (∑ i ∈ Finset.range (NN + 1), |CR i|) * |y - z| :=
  sum_Hk_lipschitz NN eR CR hy hz

/-- One-sided form: `U(y) ≤ U(z) + 47 (∑ |Cᵢ|) |y - z|`. -/
theorem UR_le_add {y z : ℝ} (hy : ∀ i ≤ NN, |eR i - y| ≤ 22) (hz : ∀ i ≤ NN, |eR i - z| ≤ 22) :
    UR y ≤ UR z + 47 * (∑ i ∈ Finset.range (NN + 1), |CR i|) * |y - z| := by
  have h := UR_lipschitz hy hz
  have := le_abs_self (UR y - UR z)
  linarith

end TPMahler.Cert
