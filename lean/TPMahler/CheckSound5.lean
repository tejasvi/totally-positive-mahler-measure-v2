import TPMahler.CheckSound4

/-!
# Soundness of the checker, part 5: global constants and the polynomial fold of a chord leaf
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-! ## Global constants of the context -/

theorem ctx_tab : (mkCtx iLoNum 128).tab = TAB := rfl
theorem ctx_l2 : (mkCtx iLoNum 128).l2 = L2 := rfl
theorem ctx_rs : (mkCtx iLoNum 128).rs = mkRecs GS nodes gvals := rfl

theorem sDen_pos : 0 < sDen := by unfold sDen DEC; positivity

theorem sR_eq : sR = (sNum : ℝ) / sDen := rfl

theorem sNum_pos : 0 < sNum := by
  have h := sR_pos
  rw [sR_eq] at h
  have : (0 : ℝ) < sNum := by
    by_contra hc
    push Not at hc
    have : (sNum : ℝ) / sDen ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc (Nat.cast_nonneg _)
    linarith
  exact_mod_cast this

/-- `m0hi ≥ 2^P m₀`. -/
theorem m0hi_ge : 2 ^ P * m0 ≤ ((mkCtx iLoNum 128).m0hi : ℝ) := by
  show 2 ^ P * m0 ≤ ((cdiv ((m0num : ℤ) * 2 ^ P) m0den : ℤ) : ℝ)
  have hm : 0 < m0den := by unfold m0den; norm_num
  have h := le_cdiv ((m0num : ℤ) * 2 ^ P) (b := m0den) hm
  refine le_trans (le_of_eq ?_) h
  unfold m0 m0num m0den
  push_cast
  ring

set_option maxRecDepth 100000 in
/-- `isLo ≤ 2^P I / s`, given `I ≥ iLoNum / 2^128`. -/
theorem isLo_le (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) : ((mkCtx iLoNum 128).isLo : ℝ) ≤ 2 ^ P * (IR / sR) := by
  show ((fdiv ((iLoNum : ℤ) * (sDen : ℤ) * 2 ^ P) (sNum * 2 ^ 128) : ℤ) : ℝ) ≤ _
  have hpos : 0 < sNum * 2 ^ 128 := Nat.mul_pos sNum_pos (Nat.two_pow_pos 128)
  have h := fdiv_le ((iLoNum : ℤ) * (sDen : ℤ) * 2 ^ P) hpos
  have hs : (0 : ℝ) < sNum := by exact_mod_cast sNum_pos
  have hd : (0 : ℝ) < sDen := by exact_mod_cast sDen_pos
  refine le_trans h ?_
  calc (((iLoNum : ℤ) * (sDen : ℤ) * 2 ^ P : ℤ) : ℝ) / ((sNum * 2 ^ 128 : ℕ) : ℝ)
      = 2 ^ P * (((iLoNum : ℝ) / 2 ^ 128) / ((sNum : ℝ) / sDen)) := by
        push_cast; field_simp; norm_num
    _ ≤ 2 ^ P * (IR / ((sNum : ℝ) / sDen)) := by gcongr
    _ = 2 ^ P * (IR / sR) := by rw [sR_eq]

theorem logT_D (k : ℕ) :
    ((logT TAB L2 (DEC * 2 ^ k) 1).1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧
      2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ ((logT TAB L2 (DEC * 2 ^ k) 1).2 : ℝ) := by
  have h := logT_sound (a := DEC * 2 ^ k) (b := 1) (Nat.mul_pos (by decide) (Nat.two_pow_pos k)) one_pos
  simpa using h

theorem logT_all : ∀ a b : ℕ, 0 < a → 0 < b → ((logT TAB L2 a b).1 : ℝ) ≤ 2 ^ P * Real.log ((a : ℝ) / b) ∧
    2 ^ P * Real.log ((a : ℝ) / b) ≤ (logT TAB L2 a b).2 := fun a b ha hb => logT_sound ha hb

/-- `logPlusLo ≤ 2^P log⁺ (X/D)`. -/
theorem logPlusLo_le (X D : ℕ) (hD : 0 < D) :
    (logPlusLo (mkCtx iLoNum 128) X D : ℝ) ≤ 2 ^ P * Real.posLog ((X : ℝ) / D) := by
  unfold logPlusLo
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  split_ifs with h
  · push_cast
    exact mul_nonneg (by positivity) (Real.posLog_nonneg)
  · push Not at h
    have hX : 0 < X := lt_of_le_of_lt (Nat.zero_le _) h
    have h1 := (logT_sound (a := X) (b := D) hX hD).1
    have hgt : (1 : ℝ) ≤ (X : ℝ) / D := by
      rw [le_div_iff₀ hD']; have : (D : ℝ) < X := by exact_mod_cast h
      linarith
    rw [posLog_eq_log_of_one_le hgt]
    exact h1

/-! ## The fold over the polynomials -/

/-- The step of the fold over the polynomials in `chordLB`. -/
def polyFold (g : (List Int × ℕ × ℕ) × ℕ → Option (ℤ × ℤ × ℤ × ℤ × ℤ))
    (acc : Option (ℤ × ℤ × ℤ × ℤ × ℤ)) (x : (List Int × ℕ × ℕ) × ℕ) : Option (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  match acc with
  | none => none
  | some (ap, aq, t0, sl, mp) =>
    match g x with
    | none => none
    | some (ap', aq', t0', sl', mp') => some (ap + ap', aq + aq', t0 + t0', sl + sl', mp + mp')

theorem polyFold_some (g : (List Int × ℕ × ℕ) × ℕ → Option (ℤ × ℤ × ℤ × ℤ × ℤ)) :
    ∀ (L : List ((List Int × ℕ × ℕ) × ℕ)) (s : ℤ × ℤ × ℤ × ℤ × ℤ) (T : ℤ × ℤ × ℤ × ℤ × ℤ),
      L.foldl (polyFold g) (some s) = some T →
        (∀ x ∈ L, (g x).isSome) ∧ T = s + (L.map (fun x => (g x).getD 0)).sum := by
  intro L
  induction L with
  | nil => intro s T h; simp at h; simp [h]
  | cons x L ih =>
    intro s T h
    simp only [List.foldl_cons] at h
    cases hg : g x with
    | none =>
      have : polyFold g (some s) x = none := by simp [polyFold, hg]
      rw [this] at h
      have hn : ∀ L' : List ((List Int × ℕ × ℕ) × ℕ), L'.foldl (polyFold g) none = none := by
        intro L'; induction L' with
        | nil => rfl
        | cons y L' ih' => simp only [List.foldl_cons]; exact ih'
      rw [hn] at h; exact absurd h (by simp)
    | some v =>
      obtain ⟨a1, a2, a3, a4, a5⟩ := s
      obtain ⟨b1, b2, b3, b4, b5⟩ := v
      have : polyFold g (some (a1, a2, a3, a4, a5)) x = some (a1 + b1, a2 + b2, a3 + b3, a4 + b4, a5 + b5) := by
        simp [polyFold, hg]
      rw [this] at h
      obtain ⟨h1, h2⟩ := ih _ _ h
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · simp [hg]
        · exact h1 y hy
      · rw [h2, List.map_cons, List.sum_cons, hg]
        simp only [Option.getD_some]
        rw [← add_assoc]
        rfl

/-- The zipped list of the polynomials, weights and indices. -/
theorem polyList_eq : (List.zip polys (List.zip cwNum cwSh)).zipIdx =
    (List.range 19).map (fun j => ((polys.getD j [], (cwNum.getD j 0, cwSh.getD j 0)), j)) := by
  decide +kernel

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

end TPMahler.Cert
