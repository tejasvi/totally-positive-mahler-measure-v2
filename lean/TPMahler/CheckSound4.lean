import TPMahler.CheckSound3

/-!
# Soundness of the checker, part 4: the node pass summed over all nodes
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

theorem leafPass_range {k Xp Xq : ℕ} (hpq : Xp < Xq) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ LD.2) :
    ∀ n ≤ NN + 1,
      let D : ℕ := DEC * 2 ^ k
      let p : ℝ := Xp / D
      let q : ℝ := Xq / D
      let A := ((List.range n).map recOf).foldl (leafStep TAB L2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩
      A.inside = false →
        (∀ i < n, CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) ∧
        ((A.spl : ℝ) ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
            ∑ i ∈ Finset.range n, (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ∧
          4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
            ∑ i ∈ Finset.range n, (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ≤ (A.sph : ℝ)) ∧
        ((A.sql : ℝ) ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
            ∑ i ∈ Finset.range n, (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ∧
          4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
            ∑ i ∈ Finset.range n, (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ≤ (A.sqh : ℝ)) ∧
        (∀ x : ℝ, p < x → x < q →
          2 ^ (P + QS) * ∑ i ∈ Finset.range n, (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |x - eR i|)
            ≤ (A.m : ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro _ D p q A _
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero i), ?_, ?_, ?_⟩
    · simp [A]
    · simp [A]
    · intro x _ _; simp [A]
  | succ n ih =>
    intro hn D p q A hA
    have hfold : A = leafStep TAB L2 k Xp Xq LD
        (((List.range n).map recOf).foldl (leafStep TAB L2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩) (recOf n) := by
      simp only [A, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    set A0 := ((List.range n).map recOf).foldl (leafStep TAB L2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩ with hA0
    have hstep := leafStep_spec (k := k) (Xp := Xp) (Xq := Xq) (i := n) (by omega) hpq hLD A0
    simp only at hstep
    rw [← hfold] at hstep
    obtain ⟨hmono, hspec⟩ := hstep
    have hA0f : A0.inside = false := hmono hA
    obtain ⟨hin, ⟨hp1, hp2⟩, ⟨hq1, hq2⟩, hm⟩ := hspec hA
    obtain ⟨ihin, ⟨ihp1, ihp2⟩, ⟨ihq1, ihq2⟩, ihm⟩ := ih (by omega) hA0f
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact ihin i h
      · rw [h]; exact hin
    · rw [Finset.sum_range_succ, mul_add]; linarith
    · rw [Finset.sum_range_succ, mul_add]; linarith
    · rw [Finset.sum_range_succ, mul_add]; linarith
    · rw [Finset.sum_range_succ, mul_add]; linarith
    · intro x hx1 hx2
      have h1 := ihm x hx1 hx2
      have h2 := hm x hx1 hx2
      rw [Finset.sum_range_succ, mul_add]; linarith

/-- **The node pass of a chord leaf.** -/
theorem leafPass_sound {k Xp Xq : ℕ} (hpq : Xp < Xq) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ LD.2) :
    let D : ℕ := DEC * 2 ^ k
    let p : ℝ := Xp / D
    let q : ℝ := Xq / D
    let A := leafPass TAB L2 (mkRecs GS nodes gvals) k Xp Xq LD
    A.inside = false →
      (∀ i ≤ NN, CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) ∧
      ((A.spl : ℝ) ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
          ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ∧
        4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
          ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ≤ (A.sph : ℝ)) ∧
      ((A.sql : ℝ) ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
          ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ∧
        4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 *
          ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ≤ (A.sqh : ℝ)) ∧
      (∀ x : ℝ, p < x → x < q →
        2 ^ (P + QS) * ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |x - eR i|)
          ≤ (A.m : ℝ)) := by
  intro D p q A hA
  have hAeq : A = ((List.range (NN + 1)).map recOf).foldl (leafStep TAB L2 k Xp Xq LD) ⟨0, 0, 0, 0, 0, false⟩ := by
    simp only [A, leafPass, mkRecs_eq]
  rw [hAeq] at hA ⊢
  obtain ⟨h1, h2, h3, h4⟩ := leafPass_range hpq hLD (NN + 1) le_rfl hA
  exact ⟨fun i hi => h1 i (Nat.lt_succ_of_le hi), h2, h3, h4⟩

end TPMahler.Cert
