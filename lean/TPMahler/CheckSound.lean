import AuxCommon.LogKSound
import TPMahler.PolySound
import TPMahler.AnaSound
import TPMahler.TailSound
import TPMahler.Assembly

/-!
# Soundness of the checker, part 1: logarithm tables and node records

* `tab_ok`, `l2_ok`, `logT_sound`: the logarithm `logT TAB L2` of the checker encloses `2^P log(a/b)`.
* `recOf`, `mkRecs_eq`, `recNum_div`: the node records of the checker are `(n_i, sign C_i, ⌊2^QS C_i⌋, ⌈2^QS C_i⌉)`
  with `C_i = slopeJump NN eR GR i`.
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-! ## Tables -/

theorem tab_check : tableCheck 64 24 48 TAB 66 = true := by decide +kernel

theorem l2_check : l2Check 64 24 48 L2.1 L2.2 = true := by decide +kernel

theorem tab_ok : TableOK P TAB WT := tableCheck_sound tab_check

theorem l2_ok : ((L2.1 : ℕ) : ℝ) ≤ 2 ^ P * Real.log 2 ∧ 2 ^ P * Real.log 2 ≤ ((L2.2 : ℕ) : ℝ) :=
  l2Check_sound l2_check

/-- **The checker's logarithm is sound.** -/
theorem logT_sound {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((logT TAB L2 a b).1 : ℝ) ≤ 2 ^ P * Real.log ((a : ℝ) / b) ∧
      2 ^ P * Real.log ((a : ℝ) / b) ≤ ((logT TAB L2 a b).2 : ℝ) := by
  unfold logT
  refine logK_sound ha hb tab_ok ?_ ?_
  · have := l2_ok.1; simpa using this
  · have := l2_ok.2; simpa using this

/-! ## Node records -/

/-- Numerator of the slope of piece `k`: `(g_{k+1} - g_k) 10^10`. -/
def snI (k : ℕ) : ℤ := ((gvals.getD (k + 1) 0 : ℤ) - (gvals.getD k 0 : ℤ)) * (DEC : ℤ)
/-- Denominator of the slope of piece `k`: `(n_{k+1} - n_k) 2^GS`. -/
def sdI (k : ℕ) : ℕ := (nodes.getD (k + 1) 0 - nodes.getD k 0) * 2 ^ GS

/-- `C_i = recNum i / recDen i`. -/
def recNum (i : ℕ) : ℤ :=
  if i = 0 then snI 0 * 1 - 0 * (sdI 0 : ℤ)
  else if i < NN then snI i * (sdI (i - 1) : ℤ) - snI (i - 1) * (sdI i : ℤ)
  else -snI (NN - 1)
def recDen (i : ℕ) : ℕ :=
  if i = 0 then sdI 0 * 1 else if i < NN then sdI i * sdI (i - 1) else sdI (NN - 1)

/-- The intended record of node `i`. -/
def recOf (i : ℕ) : NRec :=
  ⟨nodes.getD i 0, Int.sign (recNum i), fdiv (recNum i * 2 ^ QS) (recDen i), cdiv (recNum i * 2 ^ QS) (recDen i)⟩

/-- The slope state before node `j`. -/
def pnOf (j : ℕ) : ℤ := if j = 0 then 0 else snI (j - 1)
def pdOf (j : ℕ) : ℕ := if j = 0 then 1 else sdI (j - 1)

theorem drop_cons_getD (l : List ℕ) {j : ℕ} (hj : j < l.length) : l.drop j = l.getD j 0 :: l.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem _ _ hj]

theorem mkRecsAux_eq : ∀ k j : ℕ, j + k = NN →
    mkRecsAux QS GS (pnOf j) (pdOf j) (nodes.drop j) (gvals.drop j) = (List.range' j (k + 1)).map recOf := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp only [add_zero] at hj
    subst hj
    have hn : nodes.drop NN = [nodes.getD NN 0] := by
      rw [drop_cons_getD nodes (by rw [nodes_length]; omega)]
      rw [List.drop_eq_nil_of_le (by rw [nodes_length])]
    have hg : gvals.drop NN = [gvals.getD NN 0] := by
      rw [drop_cons_getD gvals (by rw [gvals_length]; omega)]
      rw [List.drop_eq_nil_of_le (by rw [gvals_length])]
    rw [hn, hg]
    rw [show (0 : ℕ) + 1 = 1 from rfl, List.range'_one]
    simp only [List.map_cons, List.map_nil]
    have hNN : NN ≠ 0 := by decide
    simp only [mkRecsAux, pnOf, pdOf, if_neg hNN, recOf, recNum, recDen, lt_irrefl, if_false]
  | succ k ih =>
    intro j hj
    have hj1 : j + 1 < nodes.length := by rw [nodes_length]; omega
    have hg1 : j + 1 < gvals.length := by rw [gvals_length]; omega
    have hn : nodes.drop j = nodes.getD j 0 :: nodes.getD (j + 1) 0 :: nodes.drop (j + 2) := by
      rw [drop_cons_getD nodes (by omega), drop_cons_getD nodes hj1]
    have hg : gvals.drop j = gvals.getD j 0 :: gvals.getD (j + 1) 0 :: gvals.drop (j + 2) := by
      rw [drop_cons_getD gvals (by omega), drop_cons_getD gvals hg1]
    have hn' : nodes.getD (j + 1) 0 :: nodes.drop (j + 2) = nodes.drop (j + 1) :=
      (drop_cons_getD nodes hj1).symm
    have hg' : gvals.getD (j + 1) 0 :: gvals.drop (j + 2) = gvals.drop (j + 1) :=
      (drop_cons_getD gvals hg1).symm
    rw [hn, hg, List.range'_succ, List.map_cons]
    simp only [mkRecsAux]
    rw [hn', hg']
    have hpn : snI j = pnOf (j + 1) := by simp [pnOf]
    have hpd : sdI j = pdOf (j + 1) := by simp [pdOf]
    have hrest := ih (j + 1) (by omega)
    refine congrArg₂ List.cons ?_ ?_
    · -- the record of node j
      have hjN : j < NN := by omega
      by_cases hj0 : j = 0
      · subst hj0
        simp [recOf, recNum, recDen, pnOf, pdOf, snI, sdI]
      · simp [recOf, recNum, recDen, pnOf, pdOf, snI, sdI, hj0, hjN]
    · rw [show ((↑(gvals.getD (j + 1) 0) : ℤ) - ↑(gvals.getD j 0)) * (DEC : ℤ) = pnOf (j + 1) from hpn,
        show (nodes.getD (j + 1) 0 - nodes.getD j 0) * 2 ^ GS = pdOf (j + 1) from hpd]
      exact hrest

theorem mkRecs_eq : mkRecs GS nodes gvals = (List.range (NN + 1)).map recOf := by
  have h := mkRecsAux_eq NN 0 (by simp)
  simp only [pnOf, pdOf, List.drop_zero] at h
  rw [List.range_eq_range']
  exact h

theorem sdI_pos {k : ℕ} (hk : k < NN) : 0 < sdI k := by
  have := nodes_inc k hk
  unfold sdI
  exact Nat.mul_pos (by omega) (Nat.two_pow_pos _)

theorem slope_eq {k : ℕ} (hk : k < NN) : slope eR GR k = (snI k : ℝ) / (sdI k : ℝ) := by
  have hinc := nodes_inc k hk
  unfold slope eR GR snI sdI
  rw [Nat.cast_mul, Nat.cast_sub hinc.le]
  push_cast
  have h1 : ((nodes.getD (k + 1) 0 : ℝ) - (nodes.getD k 0 : ℝ)) ≠ 0 := by
    have : (nodes.getD k 0 : ℝ) < (nodes.getD (k + 1) 0 : ℝ) := by exact_mod_cast hinc
    linarith
  unfold DEC
  field_simp
  ring

theorem recDen_pos {i : ℕ} (hi : i ≤ NN) : 0 < recDen i := by
  have hNN : 0 < NN := by decide
  unfold recDen
  split_ifs with h0 h1
  · simpa using sdI_pos hNN
  · exact Nat.mul_pos (sdI_pos h1) (sdI_pos (by omega))
  · exact sdI_pos (by omega)

theorem recNum_div {i : ℕ} (hi : i ≤ NN) : (recNum i : ℝ) / (recDen i : ℝ) = CR i := by
  have hNN : 0 < NN := by decide
  unfold CR slopeJump recNum recDen
  by_cases h0 : i = 0
  · subst h0
    simp only [hNN, ite_true, lt_irrefl, false_and, ite_false, sub_zero, mul_one, zero_mul]
    rw [slope_eq hNN]
  · by_cases h1 : i < NN
    · have hpos1 := sdI_pos h1
      have hpos2 := sdI_pos (show i - 1 < NN by omega)
      simp only [h0, ite_false, h1, ite_true, show 0 < i ∧ i ≤ NN from ⟨by omega, hi⟩, and_self]
      rw [slope_eq h1, slope_eq (show i - 1 < NN by omega)]
      have hp1 : (sdI i : ℝ) ≠ 0 := by exact_mod_cast hpos1.ne'
      have hp2 : (sdI (i - 1) : ℝ) ≠ 0 := by exact_mod_cast hpos2.ne'
      push_cast
      field_simp
    · have hiN : i = NN := by omega
      subst hiN
      have hpos := sdI_pos (show NN - 1 < NN by omega)
      simp only [h0, ite_false, h1, show 0 < NN ∧ NN ≤ NN from ⟨hNN, le_refl _⟩, ite_true, zero_sub, and_self]
      rw [slope_eq (show NN - 1 < NN by omega)]
      push_cast
      ring

/-- The record of node `i` encloses `2^QS C_i`, and its sign field is the sign of `C_i`. -/
theorem recOf_spec {i : ℕ} (hi : i ≤ NN) :
    ((recOf i).clo : ℝ) ≤ 2 ^ QS * CR i ∧ 2 ^ QS * CR i ≤ ((recOf i).chi : ℝ) ∧
      ((recOf i).sg = 0 ↔ CR i = 0) ∧ (0 < (recOf i).sg ↔ 0 < CR i) ∧ (recOf i).n = nodes.getD i 0 := by
  have hd := recDen_pos hi
  have hdR : (0 : ℝ) < recDen i := by exact_mod_cast hd
  have hC := recNum_div hi
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · have := fdiv_le (recNum i * 2 ^ QS) hd
    show ((fdiv (recNum i * 2 ^ QS) (recDen i) : ℤ) : ℝ) ≤ _
    rw [← hC]
    push_cast at this
    calc _ ≤ ((recNum i : ℝ) * 2 ^ QS) / recDen i := this
      _ = 2 ^ QS * ((recNum i : ℝ) / recDen i) := by ring
  · have := le_cdiv (recNum i * 2 ^ QS) hd
    show _ ≤ ((cdiv (recNum i * 2 ^ QS) (recDen i) : ℤ) : ℝ)
    rw [← hC]
    push_cast at this
    calc 2 ^ QS * ((recNum i : ℝ) / recDen i) = ((recNum i : ℝ) * 2 ^ QS) / recDen i := by ring
      _ ≤ _ := this
  · show Int.sign (recNum i) = 0 ↔ CR i = 0
    rw [Int.sign_eq_zero_iff_zero, ← hC]
    constructor
    · intro h; rw [h]; simp
    · intro h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact_mod_cast h
      · exact absurd h hdR.ne'
  · show 0 < Int.sign (recNum i) ↔ 0 < CR i
    rw [Int.sign_pos_iff, ← hC]
    constructor
    · intro h; exact div_pos (by exact_mod_cast h) hdR
    · intro h
      have := (div_pos_iff_of_pos_right hdR).mp h
      exact_mod_cast this

end TPMahler.Cert
