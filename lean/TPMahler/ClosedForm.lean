import TPMahler.Measure

/-!
# Lemma 3.1 of the paper: closed forms of the potential and the energy

`pwLinClosedForm : PwLinClosedForm`, so the named hypothesis `PwLinClosedForm` holds.

Proof: two integrations by parts on each piece `[e k, e (k+1)]`. With `Hd t = t log |t| - t` and
`Ld t = t³/6 log |t| - 11 t³/36` we have `H' = Hd`, `Hd' = log |·|`, `L' = Ld`, `Ld' = H` off `0`, and all of
`H, Hd, L, Ld` are continuous. The fundamental theorem of calculus with the exceptional point `y = x` (Mathlib
`integral_eq_of_hasDerivAt_off_countable_of_le`) gives each piece; the boundary terms telescope because
`G 0 = G N = 0`, and the rest is a summation by parts against the slope jumps (`sum_slopeJump_mul`). The energy follows
from the potential formula and the same computation with `L` in place of `H` (no Fubini).
-/

open MeasureTheory Set Filter Topology

namespace TPMahler

/-- `H'(t) = t log |t| - t`. -/
noncomputable def Hd (t : ℝ) : ℝ := t * Real.log t - t

/-- `L'(t) = t³/6 log |t| - 11 t³/36`. -/
noncomputable def Ld (t : ℝ) : ℝ := t ^ 3 / 6 * Real.log t - 11 / 36 * t ^ 3

theorem Hk_eq_fun : Hk = fun t => t * Real.log t * (t / 2) - 3 / 4 * t ^ 2 := by
  funext t
  rw [Hk, Real.log_abs]
  ring

theorem Lk_eq_fun : Lk = fun t => t * Real.log t * (t ^ 3 / 24) - 25 / 288 * t ^ 4 := by
  funext t
  rw [Lk, Real.log_abs]
  ring

theorem Ld_eq_fun : Ld = fun t => t * Real.log t * (t ^ 2 / 6) - 11 / 36 * t ^ 3 := by
  funext t
  rw [Ld]
  ring

theorem Hk_neg (t : ℝ) : Hk (-t) = Hk t := by
  simp only [Hk, abs_neg]
  ring

theorem Lk_neg (t : ℝ) : Lk (-t) = Lk t := by
  simp only [Lk, abs_neg]
  ring

theorem continuous_Hk : Continuous Hk := by
  rw [Hk_eq_fun]
  exact (Real.continuous_mul_log.mul (continuous_id.div_const 2)).sub
    (continuous_const.mul (continuous_pow 2))

theorem continuous_Hd : Continuous Hd := by
  show Continuous fun t => t * Real.log t - t
  exact Real.continuous_mul_log.sub continuous_id

theorem continuous_Lk : Continuous Lk := by
  rw [Lk_eq_fun]
  exact (Real.continuous_mul_log.mul ((continuous_pow 3).div_const 24)).sub
    (continuous_const.mul (continuous_pow 4))

theorem continuous_Ld : Continuous Ld := by
  rw [Ld_eq_fun]
  exact (Real.continuous_mul_log.mul ((continuous_pow 2).div_const 6)).sub
    (continuous_const.mul (continuous_pow 3))

theorem hasDerivAt_Hk {t : ℝ} (ht : t ≠ 0) : HasDerivAt Hk (Hd t) t := by
  rw [Hk_eq_fun]
  have h := ((Real.hasDerivAt_mul_log ht).mul ((hasDerivAt_id' t).div_const 2)).sub
    ((hasDerivAt_pow 2 t).const_mul (3 / 4 : ℝ))
  convert h using 1
  simp only [Hd]
  push_cast
  ring

theorem hasDerivAt_Hd {t : ℝ} (ht : t ≠ 0) : HasDerivAt Hd (Real.log t) t := by
  have h := (Real.hasDerivAt_mul_log ht).sub (hasDerivAt_id' t)
  have hfun : Hd = (fun x => x * Real.log x) - fun x => x := by
    funext x
    simp [Hd]
  rw [hfun]
  convert h using 1
  ring

theorem hasDerivAt_Lk {t : ℝ} (ht : t ≠ 0) : HasDerivAt Lk (Ld t) t := by
  rw [Lk_eq_fun]
  have h := ((Real.hasDerivAt_mul_log ht).mul ((hasDerivAt_pow 3 t).div_const 24)).sub
    ((hasDerivAt_pow 4 t).const_mul (25 / 288 : ℝ))
  convert h using 1
  simp only [Ld]
  push_cast
  ring

theorem hasDerivAt_Ld {t : ℝ} (ht : t ≠ 0) : HasDerivAt Ld (Hk t) t := by
  rw [Ld_eq_fun]
  have h := ((Real.hasDerivAt_mul_log ht).mul ((hasDerivAt_pow 2 t).div_const 6)).sub
    ((hasDerivAt_pow 3 t).const_mul (11 / 36 : ℝ))
  convert h using 1
  rw [Hk_eq_fun]
  push_cast
  ring

/-- **One piece.** If `Φ' = φ` and `φ' = ψ` off `0`, with `Φ, φ` continuous, then
`∫_a^b ψ(y - x) A(y) dy = φ(b - x) A(b) - φ(a - x) A(a) - A' (Φ(b - x) - Φ(a - x))` for the affine `A` with
`A(a) = Ga`, `A(b) = Gb`. -/
theorem integral_piece {Φ φ ψ : ℝ → ℝ} (hΦc : Continuous Φ) (hφc : Continuous φ)
    (hΦ : ∀ t, t ≠ 0 → HasDerivAt Φ (φ t) t) (hφ : ∀ t, t ≠ 0 → HasDerivAt φ (ψ t) t) (x : ℝ) {a b : ℝ}
    (hab : a < b) (hψi : IntervalIntegrable (fun y => ψ (y - x)) volume a b) (Ga Gb : ℝ) :
    ∫ y in a..b, ψ (y - x) * ((Ga * (b - y) + Gb * (y - a)) / (b - a)) =
      φ (b - x) * Gb - φ (a - x) * Ga - (Gb - Ga) / (b - a) * (Φ (b - x) - Φ (a - x)) := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hAd : ∀ y, HasDerivAt (fun y => (Ga * (b - y) + Gb * (y - a)) / (b - a)) ((Gb - Ga) / (b - a)) y := by
    intro y
    have h := ((((hasDerivAt_id' y).const_sub b).const_mul Ga).add
      (((hasDerivAt_id' y).sub_const a).const_mul Gb)).div_const (b - a)
    convert h using 1
    ring
  have hAc : Continuous fun y : ℝ => (Ga * (b - y) + Gb * (y - a)) / (b - a) := by fun_prop
  have hFc : Continuous fun y => φ (y - x) * ((Ga * (b - y) + Gb * (y - a)) / (b - a)) -
      (Gb - Ga) / (b - a) * Φ (y - x) :=
    ((hφc.comp (continuous_id.sub continuous_const)).mul hAc).sub
      (continuous_const.mul (hΦc.comp (continuous_id.sub continuous_const)))
  have hFd : ∀ y ∈ Ioo a b \ {x}, HasDerivAt (fun y => φ (y - x) * ((Ga * (b - y) + Gb * (y - a)) / (b - a)) -
      (Gb - Ga) / (b - a) * Φ (y - x)) (ψ (y - x) * ((Ga * (b - y) + Gb * (y - a)) / (b - a))) y := by
    intro y hy
    have hyx : y - x ≠ 0 := by
      intro h
      apply hy.2
      rw [mem_singleton_iff]
      linarith
    have h1 : HasDerivAt (fun y => φ (y - x)) (ψ (y - x)) y :=
      HasDerivAt.comp_sub_const y x (hφ (y - x) hyx)
    have h2 : HasDerivAt (fun y => Φ (y - x)) (φ (y - x)) y :=
      HasDerivAt.comp_sub_const y x (hΦ (y - x) hyx)
    have := (h1.mul (hAd y)).sub (h2.const_mul ((Gb - Ga) / (b - a)))
    convert this using 1
    ring
  have hint : IntervalIntegrable (fun y => ψ (y - x) * ((Ga * (b - y) + Gb * (y - a)) / (b - a)))
      volume a b :=
    hψi.mul_continuousOn hAc.continuousOn
  rw [integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab.le (countable_singleton x) hFc.continuousOn hFd
    hint]
  field_simp
  ring

/-- Summation by parts against the slope jumps: `∑ᵢ Cᵢ uᵢ = -∑ₖ gₖ (u_{k+1} - uₖ)`. -/
theorem sum_slopeJump_mul (N : ℕ) (e G : ℕ → ℝ) (u : ℕ → ℝ) :
    ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * u i =
      -∑ k ∈ Finset.range N, slope e G k * (u (k + 1) - u k) := by
  have h1 : ∑ i ∈ Finset.range (N + 1), (if i < N then slope e G i else 0) * u i =
      ∑ k ∈ Finset.range N, slope e G k * u k := by
    rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl N), zero_mul, add_zero]
    exact Finset.sum_congr rfl (fun i hi => by rw [ite_eq_left (Finset.mem_range.mp hi)])
  have h2 : ∑ i ∈ Finset.range (N + 1), (if 0 < i ∧ i ≤ N then slope e G (i - 1) else 0) * u i =
      ∑ k ∈ Finset.range N, slope e G k * u (k + 1) := by
    rw [Finset.sum_range_succ', ite_eq_right (by simp), zero_mul, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [ite_eq_left ⟨Nat.succ_pos i, Finset.mem_range.mp hi⟩, Nat.add_sub_cancel]
  have h3 : ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * u i =
      ∑ i ∈ Finset.range (N + 1), (if i < N then slope e G i else 0) * u i -
        ∑ i ∈ Finset.range (N + 1), (if 0 < i ∧ i ≤ N then slope e G (i - 1) else 0) * u i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [slopeJump, sub_mul])
  rw [h3, h1, h2, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

section generic

variable {N : ℕ} {e G : ℕ → ℝ}

theorem mul_pwPiece_eq_indicator (ψ : ℝ → ℝ) (x : ℝ) (k : ℕ) :
    (fun y => ψ (y - x) * pwPiece e G k y) =
      Set.indicator (Ico (e k) (e (k + 1))) (fun y => ψ (y - x) * pwAff e G k y) := by
  funext y
  rw [pwPiece_eq_indicator]
  by_cases hy : y ∈ Ico (e k) (e (k + 1))
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]

theorem integrable_mul_pwLin {ψ : ℝ → ℝ} (x : ℝ)
    (hψi : ∀ a b : ℝ, IntervalIntegrable (fun y => ψ (y - x)) volume a b)
    (he : ∀ k < N, e k < e (k + 1)) : Integrable (fun y => ψ (y - x) * pwLin N e G y) := by
  have h : (fun y => ψ (y - x) * pwLin N e G y) =
      fun y => ∑ k ∈ Finset.range N, ψ (y - x) * pwPiece e G k y := by
    funext y
    rw [pwLin_eq_sum_pwPiece, Finset.mul_sum]
  rw [h]
  refine integrable_finsetSum _ (fun k hk => ?_)
  have hk := Finset.mem_range.mp hk
  rw [mul_pwPiece_eq_indicator ψ x k]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    ((intervalIntegrable_iff_integrableOn_Ico_of_le (he k hk).le).mp
      ((hψi _ _).mul_continuousOn (continuous_pwAff e G k).continuousOn))

/-- **Generic closed form.** If `Φ' = φ` and `φ' = ψ` off `0`, `Φ, φ` continuous and `ψ(· - x)` locally integrable,
then `∫ ψ(y - x) g(y) dy = ∑ᵢ Cᵢ Φ(eᵢ - x)` for `g = pwLin N e G` with `G 0 = G N = 0`. -/
theorem integral_mul_pwLin {Φ φ ψ : ℝ → ℝ} (hΦc : Continuous Φ) (hφc : Continuous φ)
    (hΦ : ∀ t, t ≠ 0 → HasDerivAt Φ (φ t) t) (hφ : ∀ t, t ≠ 0 → HasDerivAt φ (ψ t) t) (x : ℝ)
    (hψi : ∀ a b : ℝ, IntervalIntegrable (fun y => ψ (y - x)) volume a b)
    (he : ∀ k < N, e k < e (k + 1)) (hG0 : G 0 = 0) (hGN : G N = 0) :
    ∫ y, ψ (y - x) * pwLin N e G y =
      ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Φ (e i - x) := by
  have hpiece : ∀ k < N, ∫ y, ψ (y - x) * pwPiece e G k y =
      φ (e (k + 1) - x) * G (k + 1) - φ (e k - x) * G k -
        slope e G k * (Φ (e (k + 1) - x) - Φ (e k - x)) := by
    intro k hk
    rw [mul_pwPiece_eq_indicator ψ x k, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (he k hk).le]
    exact integral_piece hΦc hφc hΦ hφ x (he k hk) (hψi _ _) (G k) (G (k + 1))
  have hint : ∀ k ∈ Finset.range N, Integrable (fun y => ψ (y - x) * pwPiece e G k y) := by
    intro k hk
    have hk := Finset.mem_range.mp hk
    rw [mul_pwPiece_eq_indicator ψ x k]
    exact (integrable_indicator_iff measurableSet_Ico).mpr
      ((intervalIntegrable_iff_integrableOn_Ico_of_le (he k hk).le).mp
        ((hψi _ _).mul_continuousOn (continuous_pwAff e G k).continuousOn))
  have h : (fun y => ψ (y - x) * pwLin N e G y) =
      fun y => ∑ k ∈ Finset.range N, ψ (y - x) * pwPiece e G k y := by
    funext y
    rw [pwLin_eq_sum_pwPiece, Finset.mul_sum]
  rw [h, integral_finsetSum _ hint,
    Finset.sum_congr rfl (fun k hk => hpiece k (Finset.mem_range.mp hk)), Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun k => φ (e k - x) * G k), hG0, hGN, mul_zero, mul_zero, sub_zero, zero_sub,
    sum_slopeJump_mul]

end generic

section closedForms

variable {N : ℕ} {e G : ℕ → ℝ}

theorem intervalIntegrable_log_sub (x a b : ℝ) :
    IntervalIntegrable (fun y => Real.log (y - x)) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := a - x) (b := b - x)).comp_sub_right x
  simpa only [sub_add_cancel] using h

/-- The potential formula of Lemma 3.1: `∫ log |x - y| g(y) dy = ∑ᵢ Cᵢ H(eᵢ - x)`. -/
theorem integral_log_mul_pwLin (he : ∀ k < N, e k < e (k + 1)) (hG0 : G 0 = 0) (hGN : G N = 0)
    (x : ℝ) : ∫ y, Real.log |x - y| * pwLin N e G y =
      ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x) := by
  have h : (fun y => Real.log |x - y| * pwLin N e G y) = fun y => Real.log (y - x) * pwLin N e G y := by
    funext y
    rw [Real.log_abs, ← Real.log_neg_eq_log, neg_sub]
  rw [h]
  exact integral_mul_pwLin continuous_Hk continuous_Hd (fun _ ht => hasDerivAt_Hk ht)
    (fun _ ht => hasDerivAt_Hd ht) x (intervalIntegrable_log_sub x) he hG0 hGN

theorem intervalIntegrable_Hk_sub (z a b : ℝ) :
    IntervalIntegrable (fun y => Hk (y - z)) volume a b :=
  (continuous_Hk.comp (continuous_id.sub continuous_const)).intervalIntegrable a b

/-- `∫ H(y - z) g(y) dy = ∑ₖ Cₖ L(eₖ - z)`. -/
theorem integral_Hk_mul_pwLin (he : ∀ k < N, e k < e (k + 1)) (hG0 : G 0 = 0) (hGN : G N = 0)
    (z : ℝ) : ∫ y, Hk (y - z) * pwLin N e G y =
      ∑ k ∈ Finset.range (N + 1), slopeJump N e G k * Lk (e k - z) :=
  integral_mul_pwLin continuous_Lk continuous_Ld (fun _ ht => hasDerivAt_Lk ht)
    (fun _ ht => hasDerivAt_Ld ht) z (intervalIntegrable_Hk_sub z) he hG0 hGN

end closedForms

/-- **Lemma 3.1 of the paper** (lem:closed): the named hypothesis `PwLinClosedForm` holds. -/
theorem pwLinClosedForm : PwLinClosedForm := by
  intro N e G he hG0 hGN
  refine ⟨fun x => integral_log_mul_pwLin he hG0 hGN x, ?_⟩
  have h1 : ∀ x, ∫ y, Real.log |x - y| * pwLin N e G y * pwLin N e G x =
      ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * (Hk (x - e i) * pwLin N e G x) := by
    intro x
    rw [integral_mul_const, integral_log_mul_pwLin he hG0 hGN x, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show e i - x = -(x - e i) by ring, Hk_neg]
    ring
  rw [integral_congr_ae (ae_of_all _ h1), integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_const_mul, integral_Hk_mul_pwLin he hG0 hGN (e i), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show e k - e i = -(e i - e k) by ring, Lk_neg]
    ring
  · intro i _
    exact (integrable_mul_pwLin (e i) (intervalIntegrable_Hk_sub (e i)) he).const_mul _

end TPMahler
