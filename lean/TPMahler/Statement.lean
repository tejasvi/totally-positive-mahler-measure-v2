import AuxCommon.Basic

/-!
# Totally positive algebraic numbers: statement of the main theorem (draft, proofs pending)

Paper: "A lower bound for the smallest limit point of the absolute Mahler measure of totally positive algebraic
integers", Theorem 1.1, certificate `tp_certificate.json` (SHA-256 9f1e5115...).

For an algebraic number `α` with minimal polynomial `P ∈ ℤ[X]` (irreducible, primitive, degree `n`), the paper puts
`M(α) = a ∏ max(1, |αᵢ|)` and `log Ω(α) = log M(α) / n`. Here `M(α)` is Mathlib's `Polynomial.mahlerMeasure` of `P`
viewed in `ℂ[X]` (`Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots`).
-/

open Polynomial MeasureTheory Filter
open AuxCommon

namespace TPMahler

/-- All complex roots of `P` are positive real numbers. For a minimal polynomial of `α` this says that `α` is totally
positive. -/
def AllRootsPos (P : ℤ[X]) : Prop :=
  ∀ z ∈ (toC P).roots, 0 < z.re ∧ z.im = 0

/-- `log Ω(α) = log M(P) / deg P` for a root `α` of the minimal polynomial `P`: the absolute logarithmic Weil height. -/
noncomputable def logOmega (P : ℤ[X]) : ℝ :=
  Real.log (toC P).mahlerMeasure / P.natDegree

/-- The bound `m₀` of Theorem 1.1. -/
noncomputable def m0 : ℝ := 19152077587359311629 / 35184372088832000000

/-- Totally positive algebraic numbers `α` with `log Ω(α) ≤ B`. -/
def TPLow (B : ℝ) : Set ℂ :=
  {α | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧ logOmega P ≤ B}

/-- The values `Ω(α)` for totally positive algebraic integers `α` (the set `𝓛₊` of the paper). -/
def Lplus : Set ℝ :=
  {y | ∃ α : ℂ, IsIntegral ℤ α ∧ ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧
    y = (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹)}

/-! ## The reference measure: piecewise-linear densities and their closed forms -/

/-- The continuous piecewise-linear function with values `G k` at the nodes `e k` (`k ≤ N`), linear on each
`[e k, e (k+1)]` and `0` outside `[e 0, e N)`. -/
noncomputable def pwLin (N : ℕ) (e G : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    if e k ≤ x ∧ x < e (k + 1) then (G k * (e (k + 1) - x) + G (k + 1) * (x - e k)) / (e (k + 1) - e k) else 0

/-- Slope of `pwLin` on `[e k, e (k+1)]`. -/
noncomputable def slope (e G : ℕ → ℝ) (k : ℕ) : ℝ := (G (k + 1) - G k) / (e (k + 1) - e k)

/-- Jump `C_i` of the slope of `pwLin` at the node `e i` (the slope is `0` outside `[e 0, e N]`). -/
noncomputable def slopeJump (N : ℕ) (e G : ℕ → ℝ) (i : ℕ) : ℝ :=
  (if i < N then slope e G i else 0) - (if 0 < i ∧ i ≤ N then slope e G (i - 1) else 0)

/-- `H(t) = t²/2 log|t| - 3t²/4` (with `Real.log 0 = 0`, so `H 0 = 0`). -/
noncomputable def Hk (t : ℝ) : ℝ := t ^ 2 / 2 * Real.log |t| - 3 / 4 * t ^ 2

/-- `L(t) = t⁴/24 log|t| - 25t⁴/288`. -/
noncomputable def Lk (t : ℝ) : ℝ := t ^ 4 / 24 * Real.log |t| - 25 / 288 * t ^ 4

/-- **Named hypothesis (Lemma 3.1 of the paper, closed forms).** For a piecewise-linear `G` with `G 0 = G N = 0`,
`U_ρ(x) = ∫ log|x - y| G(y) dy = ∑ᵢ Cᵢ H(eᵢ - x)` and `I(ρ) = ∬ log|x - y| G(x) G(y) = ∑ᵢₖ Cᵢ Cₖ L(eᵢ - eₖ)`.
A calculus identity (two integrations by parts); it does not depend on the certificate. -/
def PwLinClosedForm : Prop :=
  ∀ (N : ℕ) (e G : ℕ → ℝ), (∀ k < N, e k < e (k + 1)) → G 0 = 0 → G N = 0 →
    (∀ x : ℝ, ∫ y, Real.log |x - y| * pwLin N e G y =
        ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x)) ∧
    (∫ x, ∫ y, Real.log |x - y| * pwLin N e G y * pwLin N e G x =
        ∑ i ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          slopeJump N e G i * slopeJump N e G k * Lk (e i - e k))

/-! ## Main theorem (statements; proofs in `TPMahler.Main`, pending) -/

/-- **Theorem 1.1.** For every `ε > 0` only finitely many totally positive algebraic numbers `α` satisfy
`log Ω(α) ≤ m₀ - ε`. -/
theorem tp_main (hE : EnergySmoothing) (hC : PwLinClosedForm) (ε : ℝ) (hε : 0 < ε) :
    (TPLow (m0 - ε)).Finite := by
  sorry

/-- Theorem 1.1, second form: only finitely many totally positive algebraic numbers have `Ω(α) ≤ 1.7234615`. -/
theorem tp_omega (hE : EnergySmoothing) (hC : PwLinClosedForm) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧
      (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) ≤ 17234615 / 10000000}.Finite := by
  sorry

/-- Theorem 1.1, third form: every limit point of `𝓛₊` is at least `e^{m₀}`, so `ℓ₊ ≥ e^{m₀} > 1.7234615`. -/
theorem tp_limit_point (hE : EnergySmoothing) (hC : PwLinClosedForm) :
    ∀ y : ℝ, AccPt y (𝓟 Lplus) → Real.exp m0 ≤ y := by
  sorry

theorem exp_m0_gt : (17234615 / 10000000 : ℝ) < Real.exp m0 := by
  sorry

end TPMahler
