import Mathlib

/-!
# Common definitions for the two auxiliary-function bounds

* `toC`, `IsMinpolyZ`: algebraic numbers through their minimal polynomials over `ℤ`.
* `logPot`, `logEnergy`, `DiscBound`, `CompactSupp`: logarithmic potential theory of a finite measure on `ℂ`,
  with the sign convention of the papers (`log |z - y|`, not `log (1 / |z - y|)`).
* `EnergySmoothing`: the analytic input of Lemma 2.2 of both papers (steps "Smoothing" and "Energy"), stated as a
  named hypothesis. It is a general fact of potential theory; it does not depend on any certificate.
-/

open Polynomial MeasureTheory

namespace AuxCommon

/-- An integer polynomial viewed in `ℂ[X]`. -/
noncomputable abbrev toC (P : ℤ[X]) : ℂ[X] := P.map (Int.castRingHom ℂ)

/-- `P` is a minimal polynomial of `α` over `ℤ`: irreducible in `ℤ[X]` (hence primitive), of positive degree, and
`P(α) = 0`. It is unique up to sign, and its Mahler measure does not depend on the sign. -/
def IsMinpolyZ (P : ℤ[X]) (α : ℂ) : Prop :=
  Irreducible P ∧ 0 < P.natDegree ∧ aeval α P = 0

/-- The logarithmic potential `U_ν(z) = ∫ log |z - y| dν(y)`. -/
noncomputable def logPot (ν : Measure ℂ) (z : ℂ) : ℝ := ∫ y, Real.log ‖z - y‖ ∂ν

/-- The logarithmic energy `I(ν) = ∫ U_ν dν`. -/
noncomputable def logEnergy (ν : Measure ℂ) : ℝ := ∫ z, logPot ν z ∂ν

/-- `ν(B(y, r)) ≤ K r` for every open disc of radius `0 < r ≤ 1`. -/
def DiscBound (ν : Measure ℂ) (K : ℝ) : Prop :=
  ∀ (y : ℂ) (r : ℝ), 0 < r → r ≤ 1 → (ν (Metric.ball y r)).toReal ≤ K * r

/-- `ν` has compact support. -/
def CompactSupp (ν : Measure ℂ) : Prop :=
  ∃ R : ℝ, ν (Metric.closedBall (0 : ℂ) R)ᶜ = 0

/-- **Named hypothesis (energy smoothing).** For a probability measure `ν` with compact support and
`ν(B(y, r)) ≤ K r`, distinct points `α₁, …, αₙ` and `0 < r ≤ 1`,
`(1/n) ∑ᵢ (2 U_ν(αᵢ) - I(ν)) ≥ (1/n²) ∑_{i ≠ k} log |αᵢ - αₖ| + (log r)/n - 2 K r`.
This is the combination of the steps "Smoothing" and "Energy" in the proof of Lemma 2.2 of both papers: smoothing
the conjugates over circles of radius `r` (Jensen's formula), and `I(τ - ν) ≤ 0` for the signed measure `τ - ν` of
mass zero [Saff-Totik, Lemma I.1.8]. -/
def EnergySmoothing : Prop :=
  ∀ (ν : Measure ℂ), IsProbabilityMeasure ν → ∀ K : ℝ, 0 < K → CompactSupp ν → DiscBound ν K →
    ∀ (n : ℕ) (α : Fin n → ℂ), 0 < n → Function.Injective α → ∀ r : ℝ, 0 < r → r ≤ 1 →
      (1 / (n : ℝ) ^ 2) * ∑ i, ∑ k ∈ Finset.univ.erase i, Real.log ‖α i - α k‖ + Real.log r / n - 2 * K * r
        ≤ (1 / (n : ℝ)) * ∑ i, (2 * logPot ν (α i) - logEnergy ν)

end AuxCommon
