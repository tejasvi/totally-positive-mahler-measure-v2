import TPMahler.CheckSound8

/-!
# Soundness of the checker, part 9: `windowLB_sound`

A window leaf `[Xu, Xv] / D` is checked against the value of `F` at its left end: `log⁺` is monotone, every
`|Qⱼ|` is bounded on the window by the Taylor enclosure, and `U` moves by at most `47 (∑ |Cᵢ|) (Xv - Xu) / D`.
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

theorem ctx_sumC : (mkCtx iLoNum 128).sumC = sumAbsC (mkRecs GS nodes gvals) := by
  simp only [mkCtx]

theorem foldl_add_eq_sum {α M : Type*} [AddMonoid M] (g : α → M) :
    ∀ (l : List α) (a : M), l.foldl (fun acc y => acc + g y) a = a + (l.map g).sum
  | [], a => by simp
  | y :: ys, a => by
    rw [List.foldl_cons, foldl_add_eq_sum g ys, List.map_cons, List.sum_cons, add_assoc]

theorem sumAbsC_recs : sumAbsC (mkRecs GS nodes gvals) = sumAbsC ((List.range (NN + 1)).map recOf) := by
  rw [mkRecs_eq]

theorem sumAbsC_eq (l : List NRec) : sumAbsC l = (l.map (fun r => max r.clo.natAbs r.chi.natAbs)).sum := by
  unfold sumAbsC
  rw [foldl_add_eq_sum, zero_add]

theorem sum_map_recOf (g : NRec → ℕ) :
    (((List.range (NN + 1)).map recOf).map g).sum = ∑ i ∈ Finset.range (NN + 1), g (recOf i) := by
  rw [List.map_map, list_sum_range]
  rfl

/-- `sumC` bounds `2^QS ∑ |Cᵢ|`. -/
theorem sumC_ge : 2 ^ QS * ∑ i ∈ Finset.range (NN + 1), |CR i| ≤ (sumAbsC (mkRecs GS nodes gvals) : ℝ) := by
  have key : ∀ i ≤ NN, 2 ^ QS * |CR i| ≤ ((max (recOf i).clo.natAbs (recOf i).chi.natAbs : ℕ) : ℝ) := by
    intro i hi
    obtain ⟨h1, h2, -, -, -⟩ := recOf_spec hi
    have e1 : (((recOf i).clo.natAbs : ℕ) : ℝ) = |((recOf i).clo : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have e2 : (((recOf i).chi.natAbs : ℕ) : ℝ) = |((recOf i).chi : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [Nat.cast_max, e1, e2]
    rcases le_total 0 (CR i) with hc | hc
    · rw [abs_of_nonneg hc]
      exact le_trans (le_trans h2 (le_abs_self _)) (le_max_right _ _)
    · rw [abs_of_nonpos hc]
      have h3 : 2 ^ QS * -CR i ≤ -((recOf i).clo : ℝ) := by linarith
      exact le_trans (le_trans h3 (neg_le_abs _)) (le_max_left _ _)
  rw [sumAbsC_recs, sumAbsC_eq, sum_map_recOf, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact key i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem nodes_last : nodes.getD NN 0 = 112000000000 := by decide +kernel

/-- The nodes lie in `[0, 11.2]`. -/
theorem eR_range {i : ℕ} (hi : i ≤ NN) : 0 ≤ eR i ∧ eR i ≤ 112 / 10 := by
  constructor
  · rw [← eR_zero]; exact nodes_mono eR_lt (Nat.zero_le i) hi
  · have h := nodes_mono eR_lt hi le_rfl
    have e : eR NN = 112 / 10 := by unfold eR; rw [nodes_last]; norm_num
    linarith

theorem abs_eR_sub_le {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 22) : ∀ i ≤ NN, |eR i - y| ≤ 22 := by
  intro i hi
  obtain ⟨h1, h2⟩ := eR_range hi
  rw [abs_le]; constructor <;> linarith

theorem polyZip_eq : List.zip polys (List.zip cwNum cwSh) =
    (List.range 19).map (fun j => (polys.getD j [], (cwNum.getD j 0, cwSh.getD j 0))) := by
  decide +kernel

/-- The polynomial part of `windowLB`. -/
def polyPartW (Xu H D : ℕ) (LD : ℤ × ℤ) : ℤ :=
  (List.zip polys (List.zip cwNum cwSh)).foldl
    (fun (acc : Int) (y : List Int × Nat × Nat) =>
      acc + fdiv (-(y.2.1 : Int) * ((logT TAB L2 (max (encl H (taylorR Xu D y.1)).1.natAbs
        (encl H (taylorR Xu D y.1)).2.natAbs) 1).2 - ((y.1.length - 1 : Nat) : Int) * LD.1)) (2 ^ y.2.2))
    0

theorem windowLB_eq (Xu Xv k : ℕ) : windowLB (mkCtx iLoNum 128) Xu Xv k =
    logPlusLo (mkCtx iLoNum 128) Xu (DEC * 2 ^ k) - (mkCtx iLoNum 128).m0hi + (mkCtx iLoNum 128).isLo +
      polyPartW Xu (Xv - Xu) (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) -
      2 * (uHi (pointPass TAB L2 (mkRecs GS nodes gvals) k Xu (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) +
        cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * (Xv - Xu) : ℕ) : ℤ) * 2 ^ P) (DEC * 2 ^ k * 2 ^ QS)) := by
  simp only [windowLB, polyPartW, ctx_tab, ctx_l2, ctx_rs, ctx_sumC]

theorem polyPartW_le {Xu H D : ℕ} (hD : 0 < D) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) {x : ℝ}
    (hx0 : (Xu : ℝ) / D ≤ x) (hxH : x ≤ ((Xu : ℝ) + H) / D)
    (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (polyPartW Xu H D LD : ℝ) ≤
      2 ^ P * -∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| := by
  unfold polyPartW
  rw [polyZip_eq, foldl_add_eq_sum, zero_add, List.map_map, list_sum_range, Int.cast_sum,
    ← Finset.sum_neg_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have := encl_log_term logT_all hLD hD Xu H (polys.getD j []) hx0 hxH (hQx j (Finset.mem_range.mp hj))
    (cwNum.getD j 0) (cwSh.getD j 0)
  refine le_trans this (le_of_eq ?_)
  unfold cj
  ring

/-- **Window leaves.** -/
theorem windowLB_sound {Xu Xv k : ℕ} (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR) (huv : Xu < Xv)
    (hv : (Xv : ℝ) / (DEC * 2 ^ k : ℕ) ≤ 22) {x : ℝ}
    (hx : x ∈ Icc ((Xu : ℝ) / (DEC * 2 ^ k : ℕ)) ((Xv : ℝ) / (DEC * 2 ^ k : ℕ)))
    (hQx : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) :
    (windowLB (mkCtx iLoNum 128) Xu Xv k : ℝ) / 2 ^ P ≤ FR x := by
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hQS : (0 : ℝ) < 2 ^ QS := by positivity
  rw [windowLB_eq]
  have hLDs := logT_D k
  have hU0 : 2 ^ P * UR (Xu / (DEC * 2 ^ k : ℕ)) ≤
      (uHi (pointPass TAB L2 (mkRecs GS nodes gvals) k Xu (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) : ℝ) :=
    uHi_le_of hD (pointPass_sound (X := Xu) hLDs).2
  have hxH : x ≤ ((Xu : ℝ) + ((Xv - Xu : ℕ) : ℝ)) / ((DEC * 2 ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_sub huv.le, add_sub_cancel]; exact hx.2
  have hpp := polyPartW_le (Xu := Xu) (H := Xv - Xu) hD hLDs hx.1 hxH hQx
  have hsC := sumC_ge
  have hdU := le_cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * (Xv - Xu) : ℕ) : ℤ) * 2 ^ P)
    (b := DEC * 2 ^ k * 2 ^ QS) (Nat.mul_pos hD (Nat.two_pow_pos QS))
  generalize uHi (pointPass TAB L2 (mkRecs GS nodes gvals) k Xu (logT TAB L2 (DEC * 2 ^ k) 1)) (DEC * 2 ^ k) = uh
    at hU0 ⊢
  generalize polyPartW Xu (Xv - Xu) (DEC * 2 ^ k) (logT TAB L2 (DEC * 2 ^ k) 1) = pp at hpp ⊢
  generalize cdiv (((47 * sumAbsC (mkRecs GS nodes gvals) * (Xv - Xu) : ℕ) : ℤ) * 2 ^ P)
    (DEC * 2 ^ k * 2 ^ QS) = dU at hdU ⊢
  generalize sumAbsC (mkRecs GS nodes gvals) = sC at hsC hdU
  set D : ℕ := DEC * 2 ^ k with hDdef
  set Hn : ℕ := Xv - Xu with hHn
  set u : ℝ := (Xu : ℝ) / D with hudef
  set SC : ℝ := ∑ i ∈ Finset.range (NN + 1), |CR i| with hSC
  have hSC0 : 0 ≤ SC := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hu0 : 0 ≤ u := div_nonneg (Nat.cast_nonneg _) hDR.le
  have hux : u ≤ x := hx.1
  have hx22 : x ≤ 22 := le_trans hx.2 hv
  -- the potential moves by at most `47 ∑ |Cᵢ| (Xv - Xu) / D`
  have hHD : x - u ≤ (Hn : ℝ) / D := by
    rw [hHn, Nat.cast_sub huv.le, sub_div]; linarith [hx.2]
  have hUx : UR x ≤ UR u + 47 * SC * ((Hn : ℝ) / D) := by
    have h : UR x ≤ UR u + 47 * SC * |x - u| :=
      UR_le_add (abs_eR_sub_le (le_trans hu0 hux) hx22) (abs_eR_sub_le hu0 (le_trans hux hx22))
    rw [abs_of_nonneg (by linarith)] at h
    have := mul_le_mul_of_nonneg_left hHD (mul_nonneg (by norm_num : (0 : ℝ) ≤ 47) hSC0)
    linarith
  have hUxP : 2 ^ P * UR x ≤ 2 ^ P * UR u + 2 ^ P * (47 * SC * ((Hn : ℝ) / D)) := by
    have := mul_le_mul_of_nonneg_left hUx hP.le
    linarith
  have hdU' : 2 ^ P * (47 * SC * ((Hn : ℝ) / D)) ≤ (dU : ℝ) := by
    refine le_trans ?_ hdU
    have hDQ : ((D * 2 ^ QS : ℕ) : ℝ) = (D : ℝ) * 2 ^ QS := by push_cast; ring
    rw [hDQ, le_div_iff₀ (mul_pos hDR hQS)]
    have e : 2 ^ P * (47 * SC * ((Hn : ℝ) / D)) * ((D : ℝ) * 2 ^ QS) =
        47 * (2 ^ QS * SC) * (Hn : ℝ) * 2 ^ P := by field_simp
    rw [e]
    push_cast
    have h47 : (0 : ℝ) ≤ 47 * (Hn : ℝ) * 2 ^ P :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hP.le
    nlinarith
  -- `log⁺` at the left end
  have hpl : ((logPlusLo (mkCtx iLoNum 128) Xu D : ℤ) : ℝ) ≤ 2 ^ P * Real.posLog x := by
    have h1 : ((logPlusLo (mkCtx iLoNum 128) Xu D : ℤ) : ℝ) ≤ 2 ^ P * Real.posLog u := logPlusLo_le Xu D hD
    have h2 := mul_le_mul_of_nonneg_left (posLog_le_posLog hu0 hux) hP.le
    linarith
  have h2 := isLo_le hI
  have h3 := m0hi_ge
  have hFR : FR x = Real.posLog x - m0 - ∑ j ∈ Finset.range 19, cj j * Real.log |(QR (polys.getD j [])).eval x| -
      2 * UR x + IR / sR := by
    unfold FR; rw [FR_poly_sum]
  rw [hFR, div_le_iff₀ hP]
  push_cast
  linarith

end TPMahler.Cert
