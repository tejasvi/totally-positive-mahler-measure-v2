import TPMahler.CheckSound6

/-!
# Soundness of the checker, part 7: the chord leaf theorem
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

theorem convexOn_finset_sum {s : Set ℝ} (hs : Convex ℝ s) (u : Finset ℕ) (f : ℕ → ℝ → ℝ)
    (hf : ∀ j ∈ u, ConvexOn ℝ s (f j)) : ConvexOn ℝ s (fun x => ∑ j ∈ u, f j x) := by
  induction u using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | insert a u ha ih =>
    have h1 := hf a (Finset.mem_insert_self a u)
    have h2 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have := h1.add h2
    convert this using 1
    funext x
    rw [Finset.sum_insert ha]
    rfl

/-- `2^P u ≤ uHi S D` from `4 · 2^(P+QS) D² u ≤ S.2`. -/
theorem uHi_le_of {D : ℕ} (hD : 0 < D) {S : ℤ × ℤ} {u : ℝ}
    (hS : 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * u ≤ (S.2 : ℝ)) : 2 ^ P * u ≤ (uHi S D : ℝ) := by
  have hden : 0 < D * D * 2 ^ (QS + 2) := by positivity
  have h := le_cdiv S.2 hden
  unfold uHi
  refine le_trans ?_ h
  rw [le_div_iff₀ (by exact_mod_cast hden)]
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have h2 : (2 : ℝ) ^ (QS + 2) = 2 ^ QS * 4 := by rw [pow_add]; norm_num
  rw [hPQ] at hS
  push_cast
  rw [h2]
  have e : 2 ^ P * u * ((D : ℝ) * D * (2 ^ QS * 4)) = 4 * (2 ^ P * 2 ^ QS) * (D : ℝ) ^ 2 * u := by ring
  linarith

/-- The correction term of a chord leaf: `2^P max(M, 0) h² / 8 ≤ corr`. -/
theorem corr_ge {m : ℤ} {H D : ℕ} (hD : 0 < D) {mp : ℤ} (hmp : 0 ≤ mp) {M : ℝ}
    (hM : M * ((H : ℝ) / D) ^ 2 * 2 ^ P ≤ (m : ℝ) * H * H / (D * D * 2 ^ QS) + mp) :
    2 ^ P * (max M 0 * ((H : ℝ) / D) ^ 2 / 8) ≤
      (cdiv ((if 0 < m then cdiv (m * (H : ℤ) * (H : ℤ)) (D * D * 2 ^ QS) else 0) + mp) 8 : ℝ) := by
  have hden : 0 < D * D * 2 ^ QS := by positivity
  set mn : ℤ := if 0 < m then cdiv (m * (H : ℤ) * (H : ℤ)) (D * D * 2 ^ QS) else 0 with hmn
  have hmn0 : (0 : ℝ) ≤ mn := by
    rw [hmn]; split_ifs with h
    · have := le_cdiv (m * (H : ℤ) * (H : ℤ)) hden
      have hpos : (0 : ℝ) ≤ (m * (H : ℤ) * (H : ℤ) : ℤ) / ((D * D * 2 ^ QS : ℕ) : ℝ) := by
        apply div_nonneg _ (by positivity)
        have : (0 : ℝ) < m := by exact_mod_cast h
        push_cast; positivity
      linarith
    · simp
  have hmn1 : (m : ℝ) * H * H / (D * D * 2 ^ QS) ≤ mn := by
    rw [hmn]; split_ifs with h
    · have := le_cdiv (m * (H : ℤ) * (H : ℤ)) hden
      push_cast at this ⊢; exact this
    · push Not at h
      have : (m : ℝ) ≤ 0 := by exact_mod_cast h
      push_cast
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : (0 : ℝ) ≤ (H : ℝ) * H := by positivity
      nlinarith
  have h8 := le_cdiv (mn + mp) (b := 8) (by norm_num)
  refine le_trans ?_ h8
  have hmp' : (0 : ℝ) ≤ mp := by exact_mod_cast hmp
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  push_cast
  rcases le_total M 0 with hM0 | hM0
  · rw [max_eq_right hM0]
    simp only [zero_mul, zero_div, mul_zero]
    apply div_nonneg _ (by norm_num); linarith
  · rw [max_eq_left hM0]
    have : 2 ^ P * (M * ((H : ℝ) / D) ^ 2 / 8) = (M * ((H : ℝ) / D) ^ 2 * 2 ^ P) / 8 := by ring
    rw [this]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith

/-- The weight of polynomial `j`. -/
noncomputable def cj (j : ℕ) : ℝ := (cwNum.getD j 0 : ℝ) / 2 ^ (cwSh.getD j 0)

theorem FR_poly_sum (x : ℝ) : ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| =
    ∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| := by
  exact Fin.sum_univ_eq_sum_range (fun j => cj j * Real.log |(QR (polys.getD j [])).eval x|) JJ

/-- Splitting a sum by a predicate. -/
theorem sum_split_if (s : Finset ℕ) (b : ℕ → Bool) (f : ℕ → ℝ) :
    ∑ j ∈ s, f j = ∑ j ∈ s, (if b j then 0 else f j) + ∑ j ∈ s, (if b j then f j else 0) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end TPMahler.Cert
