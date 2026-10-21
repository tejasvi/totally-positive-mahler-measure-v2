import TPMahler.CheckSound7

/-!
# Soundness of the checker, part 8: `chordLB_sound`
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-- **Chord leaves.** -/
theorem chordLB_sound {Xp Xq k : ℕ} {x0q : Bool} {mask : ℕ} {lp lq : ℤ}
    (hI : (iLoNum : ℝ) / 2 ^ 128 ≤ IR)
    (h : chordLB (mkCtx iLoNum 128) Xp Xq k x0q mask = some (lp, lq)) :
    ∀ x ∈ Icc ((Xp : ℝ) / (DEC * 2 ^ k : ℕ)) ((Xq : ℝ) / (DEC * 2 ^ k : ℕ)),
      min (lp : ℝ) lq / 2 ^ P ≤ FR x := by
  intro x hx
  have hD : 0 < DEC * 2 ^ k := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < ((DEC * 2 ^ k : ℕ) : ℝ) := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  unfold chordLB at h
  dsimp only at h
  rw [ctx_tab, ctx_l2, ctx_rs] at h
  by_cases hcond : Xp < Xq ∧ ¬ (Xp < DEC * 2 ^ k ∧ DEC * 2 ^ k < Xq) ∧ Xq - Xp ≤ DEC * 2 ^ k
  swap
  · rw [if_neg hcond] at h; exact absurd h (by simp)
  rw [if_pos hcond] at h
  obtain ⟨hpq, hn1, hHD⟩ := hcond
  set D : ℕ := DEC * 2 ^ k with hDdef
  set p : ℝ := (Xp : ℝ) / D with hpdef
  set q : ℝ := (Xq : ℝ) / D with hqdef
  have hpqR : p < q := div_lt_div_of_pos_right (by exact_mod_cast hpq) hDR
  have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) hDR.le
  have hqp1 : q - p ≤ 1 := by
    rw [hpdef, hqdef, ← sub_div, div_le_one hDR]
    have : ((Xq - Xp : ℕ) : ℝ) ≤ D := by exact_mod_cast hHD
    rw [Nat.cast_sub hpq.le] at this; linarith
  have hone : ¬ (p < 1 ∧ 1 < q) := by
    rintro ⟨h1, h2⟩
    apply hn1
    constructor
    · have : (Xp : ℝ) < D := by rw [hpdef, div_lt_one hDR] at h1; exact h1
      exact_mod_cast this
    · have : (D : ℝ) < Xq := by rw [hqdef, one_lt_div hDR] at h2; exact h2
      exact_mod_cast this
  set LD := logT TAB L2 D 1 with hLD
  have hLDs := logT_D k
  set r := leafPass TAB L2 (mkRecs GS nodes gvals) k Xp Xq LD with hr
  cases hri : r.inside
  swap
  · simp only [hri, if_true] at h; exact absurd h (by simp)
  simp only [hri, Bool.false_eq_true, if_false] at h
  obtain ⟨hnin, ⟨hsp1, hsp2⟩, ⟨hsq1, hsq2⟩, hmr⟩ := leafPass_sound hpq hLDs hri
  -- the fold over the polynomials
  split at h
  · exact absurd h (by simp)
  rename_i pap paq t0 sl mp hpr
  have hpr' : (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
      (polyFold (fun x => polyLeaf TAB L2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2))
      (some (0, 0, 0, 0, 0)) = some (pap, paq, t0, sl, mp) := hpr
  obtain ⟨v, hv, hT⟩ := polyRes_facts hpr'
  have hT1 : pap = ∑ j ∈ Finset.range 19, (v j).1 := by rw [show pap = (pap, paq, t0, sl, mp).1 from rfl, hT, Prod.fst_sum]
  have hT2 : paq = ∑ j ∈ Finset.range 19, (v j).2.1 := by
    rw [show paq = (pap, paq, t0, sl, mp).2.1 from rfl, hT, Prod.snd_sum, Prod.fst_sum]
  have hT3 : t0 = ∑ j ∈ Finset.range 19, (v j).2.2.1 := by
    rw [show t0 = (pap, paq, t0, sl, mp).2.2.1 from rfl, hT, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
  have hT4 : sl = ∑ j ∈ Finset.range 19, (v j).2.2.2.1 := by
    rw [show sl = (pap, paq, t0, sl, mp).2.2.2.1 from rfl, hT, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Prod.fst_sum]
  have hT5 : mp = ∑ j ∈ Finset.range 19, (v j).2.2.2.2 := by
    rw [show mp = (pap, paq, t0, sl, mp).2.2.2.2 from rfl, hT, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum, Prod.snd_sum]
  -- per-polynomial facts
  set Qj : ℕ → ℝ[X] := fun j => QR (polys.getD j []) with hQj
  have hroot : ∀ j < 19, ∀ y ∈ Icc p q, (Qj j).eval y ≠ 0 := fun j hj =>
    polyLeaf_eval_ne_zero hD hpq (hv j hj)
  have hnc : ∀ j < 19, Nat.testBit mask j = false →
      ((v j).1 : ℝ) ≤ 2 ^ P * (-cj j * Real.log |(Qj j).eval p|) ∧
      ((v j).2.1 : ℝ) ≤ 2 ^ P * (-cj j * Real.log |(Qj j).eval q|) ∧
      (v j).2.2.1 = 0 ∧ (v j).2.2.2.1 = 0 ∧ 0 ≤ (v j).2.2.2.2 ∧
      ∀ y ∈ Icc p q, cj j * (((derivative (Qj j)).eval y) ^ 2 -
        (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2 * (q - p) ^ 2 ≤
          ((v j).2.2.2.2 : ℝ) / 2 ^ P := by
    intro j hj hbj
    have h' := hv j hj
    rw [show v j = ((v j).1, (v j).2.1, (v j).2.2.1, (v j).2.2.2.1, (v j).2.2.2.2) from rfl] at h'
    exact polyLeaf_noconv logT_all hLDs hD hpq h' hbj
  have hcv : ∀ j < 19, Nat.testBit mask j = true →
      (v j).1 = 0 ∧ (v j).2.1 = 0 ∧ (v j).2.2.2.2 = 0 ∧
      ConvexOn ℝ (Icc p q) (fun y => -cj j * Real.log |(Qj j).eval y|) ∧
      ((v j).2.2.1 : ℝ) ≤ 2 ^ P * (-cj j * Real.log |(Qj j).eval (if x0q then q else p)|) ∧
      ((v j).2.2.2.1 : ℝ) ≤ 2 ^ P * (-cj j * ((derivative (Qj j)).eval (if x0q then q else p) /
        (Qj j).eval (if x0q then q else p))) * ((if x0q then p else q) - (if x0q then q else p)) := by
    intro j hj hbj
    have h' := hv j hj
    rw [show v j = ((v j).1, (v j).2.1, (v j).2.2.1, (v j).2.2.2.1, (v j).2.2.2.2) from rfl] at h'
    exact polyLeaf_conv logT_all hLDs hD hpq h' hbj
  -- the decomposition F = A + TP + TS on [p, q]
  set sN : Finset ℕ := (Finset.range (NN + 1)).filter (fun i => ¬ singI k Xp Xq i ∧ CR i ≠ 0) with hsN
  set sS : Finset ℕ := (Finset.range (NN + 1)).filter (fun i => singI k Xp Xq i) with hsS
  set Uns : ℝ → ℝ := fun y => ∑ i ∈ sN, CR i * Hk (eR i - y) with hUns
  set Us : ℝ → ℝ := fun y => ∑ i ∈ sS, CR i * Hk (eR i - y) with hUs
  have hU : ∀ y, UR y = Uns y + Us y := by
    intro y
    simp only [UR, hUns, hUs, hsN, hsS, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : singI k Xp Xq i
    · simp [hs]
    · by_cases hc : CR i = 0
      · simp [hs, hc]
      · simp [hs, hc]
  have hUns_if : ∀ y, Uns y = ∑ i ∈ Finset.range (NN + 1), (if singI k Xp Xq i then 0 else CR i * Hk (eR i - y)) := by
    intro y
    simp only [hUns, hsN, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hs : singI k Xp Xq i
    · simp [hs]
    · by_cases hc : CR i = 0
      · simp [hs, hc]
      · simp [hs, hc]
  set A : ℝ → ℝ := fun y => Real.posLog y - m0 -
    ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval y|) -
    2 * Uns y + IR / sR with hA
  set TP : ℝ → ℝ := fun y =>
    ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then -cj j * Real.log |(Qj j).eval y| else 0) with hTP
  set TS : ℝ → ℝ := fun y => -2 * Us y with hTS
  have hF : ∀ y, FR y = A y + TP y + TS y := by
    intro y
    have hs := sum_split_if (Finset.range 19) (fun j => Nat.testBit mask j)
      (fun j => cj j * Real.log |(Qj j).eval y|)
    have hneg : ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then -cj j * Real.log |(Qj j).eval y| else 0) =
        -∑ j ∈ Finset.range 19, (if Nat.testBit mask j then cj j * Real.log |(Qj j).eval y| else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
    simp only [FR, hA, hTP, hTS, FR_poly_sum, hU y]
    simp only [hQj] at hs hneg
    rw [hs, hneg]
    ring
  -- derivatives of A on (p, q)
  obtain ⟨f', f'', hpl⟩ := posLog_chord_data hp0 hone
  have hsNx : ∀ y ∈ Ioo p q, ∀ i ∈ sN, eR i ≠ y := by
    intro y hy i hi he
    simp only [hsN, Finset.mem_filter, Finset.mem_range] at hi
    exact hnin i (by omega) hi.2.2 ⟨he ▸ hy.1, he ▸ hy.2⟩
  set A' : ℝ → ℝ := fun y => f' y -
    ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * ((derivative (Qj j)).eval y / (Qj j).eval y)) -
    2 * ∑ i ∈ sN, -(CR i * ((eR i - y) * Real.log |eR i - y| - (eR i - y))) with hA'
  set A'' : ℝ → ℝ := fun y => f'' y +
    ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * (((derivative (Qj j)).eval y) ^ 2 -
      (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2) -
    2 * ∑ i ∈ sN, CR i * Real.log |eR i - y| with hA''
  have hdA : ∀ y ∈ Ioo p q, HasDerivAt A (A' y) y := by
    intro y hy
    have hyI : y ∈ Icc p q := Ioo_subset_Icc_self hy
    have h1 := (hpl y hy).1
    have h2 : HasDerivAt (fun z => ∑ j ∈ Finset.range 19,
        (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval z|))
        (∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else
          cj j * ((derivative (Qj j)).eval y / (Qj j).eval y))) y := by
      apply HasDerivAt.fun_sum
      intro j hj
      by_cases hbj : Nat.testBit mask j
      · simp only [hbj, if_true]; exact hasDerivAt_const y 0
      · simp only [hbj, Bool.false_eq_true, if_false]
        have := (hasDerivAt_neg_mul_log_abs_eval (Qj j) (cj j)
          (hroot j (Finset.mem_range.mp hj) y hyI)).neg
        convert this using 1
        · funext z; simp only [Pi.neg_apply]; ring
        all_goals ring
    have h3 := hasDerivAt_sum_Hk sN CR eR y
    have := ((h1.sub_const m0).sub h2).sub (h3.const_mul 2) |>.add_const (IR / sR)
    convert this using 1
  have hdA' : ∀ y ∈ Ioo p q, HasDerivAt A' (A'' y) y := by
    intro y hy
    have hyI : y ∈ Icc p q := Ioo_subset_Icc_self hy
    have h1 := (hpl y hy).2.1
    have h2 : HasDerivAt (fun z => ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else
          cj j * ((derivative (Qj j)).eval z / (Qj j).eval z)))
        (∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else -(cj j * (((derivative (Qj j)).eval y) ^ 2 -
          (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2))) y := by
      apply HasDerivAt.fun_sum
      intro j hj
      by_cases hbj : Nat.testBit mask j
      · simp only [hbj, if_true]; exact hasDerivAt_const y 0
      · simp only [hbj, Bool.false_eq_true, if_false]
        have := (hasDerivAt_neg_mul_logDeriv_eval (Qj j) (cj j)
          (hroot j (Finset.mem_range.mp hj) y hyI)).neg
        convert this using 1
        · funext z; simp only [Pi.neg_apply]; ring
        all_goals ring
    have h3 := hasDerivAt_sum_Hd sN CR eR (hsNx y hy)
    have := (h1.sub h2).sub (h3.const_mul 2)
    convert this using 1
    have hsum : (∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else -(cj j * (((derivative (Qj j)).eval y) ^ 2 -
          (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2))) =
        -(∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * (((derivative (Qj j)).eval y) ^ 2 -
          (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2)) := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; split_ifs <;> ring
    simp only [hA'']
    rw [hsum]
    ring
  -- the curvature bound
  have hh0 : 0 < q - p := by linarith
  set M : ℝ := (r.m : ℝ) / 2 ^ (P + QS) +
    ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else ((v j).2.2.2.2 : ℝ) / (2 ^ P * (q - p) ^ 2))
    with hMdef
  have hM : ∀ y ∈ Ioo p q, A'' y ≤ M := by
    intro y hy
    have hyI : y ∈ Icc p q := Ioo_subset_Icc_self hy
    have h1 := (hpl y hy).2.2
    have h2 : ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * (((derivative (Qj j)).eval y) ^ 2 -
          (Qj j).eval y * (derivative (derivative (Qj j))).eval y) / ((Qj j).eval y) ^ 2) ≤
        ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else ((v j).2.2.2.2 : ℝ) / (2 ^ P * (q - p) ^ 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hbj : Nat.testBit mask j
      · simp only [hbj, if_true, le_refl]
      · simp only [hbj, Bool.false_eq_true, if_false]
        have := (hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).2.2.2.2.2 y hyI
        rw [le_div_iff₀ (mul_pos hP (pow_pos hh0 2))]
        have e : cj j * (((derivative (Qj j)).eval y) ^ 2 - (Qj j).eval y * (derivative (derivative (Qj j))).eval y) /
            ((Qj j).eval y) ^ 2 * (2 ^ P * (q - p) ^ 2) =
            (cj j * (((derivative (Qj j)).eval y) ^ 2 - (Qj j).eval y * (derivative (derivative (Qj j))).eval y) /
            ((Qj j).eval y) ^ 2 * (q - p) ^ 2) * 2 ^ P := by ring
        rw [e]
        calc _ ≤ ((v j).2.2.2.2 : ℝ) / 2 ^ P * 2 ^ P := mul_le_mul_of_nonneg_right this hP.le
          _ = ((v j).2.2.2.2 : ℝ) := by field_simp
    have h3 : -2 * ∑ i ∈ sN, CR i * Real.log |eR i - y| ≤ (r.m : ℝ) / 2 ^ (P + QS) := by
      have hm := hmr y hy.1 hy.2
      have heq : ∑ i ∈ Finset.range (NN + 1),
          (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |y - eR i|) =
          -2 * ∑ i ∈ sN, CR i * Real.log |eR i - y| := by
        rw [Finset.mul_sum, hsN, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hs : singI k Xp Xq i
        · simp [hs]
        · by_cases hc : CR i = 0
          · simp [hs, hc]
          · simp only [hs, not_false_eq_true, hc, ne_eq, and_self, if_true, if_false]
            rw [abs_sub_comm]; ring
      rw [heq] at hm
      rw [le_div_iff₀ (by positivity)]
      linarith
    simp only [hA'', hMdef]
    linarith
  -- the convex part and its tangent
  set x0 : ℝ := if x0q then q else p with hx0def
  have hx0 : x0 = p ∨ x0 = q := by
    cases x0q
    · left; simp [hx0def]
    · right; simp [hx0def]
  have hx0I : x0 ∈ Icc p q := by
    rcases hx0 with h0 | h0 <;> rw [h0]
    · exact ⟨le_rfl, hpqR.le⟩
    · exact ⟨hpqR.le, le_rfl⟩
  have hTPconv : ConvexOn ℝ (Icc p q) TP := by
    apply convexOn_finset_sum (convex_Icc p q) (Finset.range 19)
      (fun j y => if Nat.testBit mask j then -cj j * Real.log |(Qj j).eval y| else 0)
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · simp only [hbj, if_true]
      exact (hcv j (Finset.mem_range.mp hj) hbj).2.2.2.1
    · simp only [hbj, Bool.false_eq_true, if_false]
      exact convexOn_const 0 (convex_Icc p q)
  set d : ℝ := ∑ j ∈ Finset.range 19,
    (if Nat.testBit mask j then -cj j * ((derivative (Qj j)).eval x0 / (Qj j).eval x0) else 0) with hd
  have hdTP : HasDerivAt TP d x0 := by
    apply HasDerivAt.fun_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · simp only [hbj, if_true]
      exact hasDerivAt_neg_mul_log_abs_eval (Qj j) (cj j) (hroot j (Finset.mem_range.mp hj) x0 hx0I)
    · simp only [hbj, Bool.false_eq_true, if_false]
      exact hasDerivAt_const x0 0
  -- the singular terms are nonnegative
  have hTSnn : ∀ y ∈ Icc p q, 0 ≤ TS y := by
    intro y hy
    have hle : ∑ i ∈ sS, CR i * Hk (eR i - y) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      simp only [hsS, Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨_, hCpos, hend⟩ := hi
      have hei : eR i = p ∨ eR i = q := by
        have hval : ∀ X : ℕ, nodes.getD i 0 * 2 ^ k = X → eR i = (X : ℝ) / D := by
          intro X hX
          rw [← hX]
          show (nodes.getD i 0 : ℝ) / 10 ^ 10 = ((nodes.getD i 0 * 2 ^ k : ℕ) : ℝ) / ((DEC * 2 ^ k : ℕ) : ℝ)
          unfold DEC; push_cast; field_simp; norm_num
        rcases hend with h1 | h1
        · left; exact hval Xp h1
        · right; exact hval Xq h1
      have habs : |eR i - y| ≤ 1 := by
        rcases hei with h1 | h1 <;> rw [h1, abs_le] <;> constructor <;> linarith [hy.1, hy.2]
      exact mul_nonpos_of_nonneg_of_nonpos hCpos.le (Hk_nonpos habs)
    simp only [hTS, hUs]
    linarith
  -- restate the record bounds in terms of `r`, then freeze `r` so that no tactic evaluates it
  have hsp2' : 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * Uns p ≤ (r.sph : ℝ) := by
    rw [hUns_if p]; exact hsp2
  have hsq2' : 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * Uns q ≤ (r.sqh : ℝ) := by
    rw [hUns_if q]; exact hsq2
  clear_value r
  have hDne : (D : ℝ) ≠ 0 := hDR.ne'
  -- continuity of A on [p, q]
  have hpolyD : ∀ y ∈ Icc p q, HasDerivAt (fun z => ∑ j ∈ Finset.range 19,
      (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval z|))
      (∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else
        cj j * ((derivative (Qj j)).eval y / (Qj j).eval y))) y := by
    intro y hyI
    apply HasDerivAt.fun_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · simp only [hbj, if_true]; exact hasDerivAt_const y 0
    · simp only [hbj, Bool.false_eq_true, if_false]
      have := (hasDerivAt_neg_mul_log_abs_eval (Qj j) (cj j)
        (hroot j (Finset.mem_range.mp hj) y hyI)).neg
      convert this using 1
      · funext z; simp only [Pi.neg_apply]; ring
      all_goals ring
  have hAcont : ContinuousOn A (Icc p q) := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    have c1 : ContinuousAt Real.posLog y := Real.continuous_posLog.continuousAt
    have c2 := (hpolyD y hy).continuousAt
    have c3 : ContinuousAt Uns y := (hasDerivAt_sum_Hk sN CR eR y).continuousAt
    exact (((c1.sub continuousAt_const).sub c2).sub (c3.const_mul 2)).add continuousAt_const
  -- the chord and tangent bound
  have hcomb := chord_tangent_combine hpqR hAcont hdA hdA' hM hTPconv hx0 hdTP hTSnn x hx
  rw [← hF x] at hcomb
  -- the checker's values
  have hpap : (pap : ℝ) ≤ 2 ^ P * -∑ j ∈ Finset.range 19,
      (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval p|) := by
    rw [hT1]; push_cast
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · rw [(hcv j (Finset.mem_range.mp hj) hbj).1]; simp [hbj]
    · simp only [hbj, Bool.false_eq_true, if_false]
      have := (hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).1
      linarith
  have hpaq : (paq : ℝ) ≤ 2 ^ P * -∑ j ∈ Finset.range 19,
      (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval q|) := by
    rw [hT2]; push_cast
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · rw [(hcv j (Finset.mem_range.mp hj) hbj).2.1]; simp [hbj]
    · simp only [hbj, Bool.false_eq_true, if_false]
      have := (hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).2.1
      linarith
  have ht0 : (t0 : ℝ) ≤ 2 ^ P * TP x0 := by
    rw [hT3]; push_cast
    simp only [hTP, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · simp only [hbj, if_true]
      exact (hcv j (Finset.mem_range.mp hj) hbj).2.2.2.2.1
    · rw [(hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).2.2.1]; simp [hbj]
  have hsl : (sl : ℝ) ≤ 2 ^ P * d * ((if x0q then p else q) - x0) := by
    rw [hT4]; push_cast
    simp only [hd, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · simp only [hbj, if_true]
      exact (hcv j (Finset.mem_range.mp hj) hbj).2.2.2.2.2
    · rw [(hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).2.2.2.1]; simp [hbj]
  have hmp0 : 0 ≤ mp := by
    rw [hT5]
    apply Finset.sum_nonneg
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · rw [(hcv j (Finset.mem_range.mp hj) hbj).2.2.1]
    · exact (hnc j (Finset.mem_range.mp hj) (by simpa using hbj)).2.2.2.2.1
  have hHq : ((Xq - Xp : ℕ) : ℝ) / D = q - p := by
    rw [Nat.cast_sub hpq.le, sub_div]
  have hmpsum : (mp : ℝ) = ∑ j ∈ Finset.range 19,
      (if Nat.testBit mask j then 0 else ((v j).2.2.2.2 : ℝ)) := by
    rw [hT5]; push_cast
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hbj : Nat.testBit mask j
    · rw [(hcv j (Finset.mem_range.mp hj) hbj).2.2.1]; simp [hbj]
    · simp [hbj]
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have e1a : (r.m : ℝ) / 2 ^ (P + QS) * (q - p) ^ 2 * 2 ^ P =
      (r.m : ℝ) * ((q - p) * D) * ((q - p) * D) / (D * D * 2 ^ QS) := by
    rw [hPQ]; field_simp
  have e1b : (∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else
      ((v j).2.2.2.2 : ℝ) / (2 ^ P * (q - p) ^ 2))) * (q - p) ^ 2 * 2 ^ P =
      ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else ((v j).2.2.2.2 : ℝ)) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · ring
    · field_simp
  have e2 : ((Xq - Xp : ℕ) : ℝ) = (q - p) * D := by
    rw [← hHq, div_mul_cancel₀ _ hDne]
  have hMh : M * (((Xq - Xp : ℕ) : ℝ) / D) ^ 2 * 2 ^ P ≤
      (r.m : ℝ) * (Xq - Xp : ℕ) * (Xq - Xp : ℕ) / (D * D * 2 ^ QS) + mp := by
    rw [hHq, hMdef, hmpsum, add_mul, add_mul, e1a, e1b, e2]
  have hcorr := corr_ge hD hmp0 hMh
  rw [hHq] at hcorr
  have h1p : ((logPlusLo (mkCtx iLoNum 128) Xp D : ℤ) : ℝ) ≤ 2 ^ P * Real.posLog p := logPlusLo_le Xp D hD
  have h1q : ((logPlusLo (mkCtx iLoNum 128) Xq D : ℤ) : ℝ) ≤ 2 ^ P * Real.posLog q := logPlusLo_le Xq D hD
  have h2 := isLo_le hI
  have h3 := m0hi_ge
  have h4p : 2 ^ P * Uns p ≤ (uHi (r.spl, r.sph) D : ℝ) := uHi_le_of hD hsp2'
  have h4q : 2 ^ P * Uns q ≤ (uHi (r.sql, r.sqh) D : ℝ) := uHi_le_of hD hsq2'
  have hAp : A p = Real.posLog p - m0 -
      ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval p|) -
      2 * Uns p + IR / sR := rfl
  have hAq : A q = Real.posLog q - m0 -
      ∑ j ∈ Finset.range 19, (if Nat.testBit mask j then 0 else cj j * Real.log |(Qj j).eval q|) -
      2 * Uns q + IR / sR := rfl
  -- the final comparison
  have hfin : ∀ Lp Lq : ℤ,
      (Lp : ℝ) ≤ 2 ^ P * (A p + TP x0 + d * (p - x0) - max M 0 * (q - p) ^ 2 / 8) →
      (Lq : ℝ) ≤ 2 ^ P * (A q + TP x0 + d * (q - x0) - max M 0 * (q - p) ^ 2 / 8) →
      min (Lp : ℝ) Lq / 2 ^ P ≤ FR x := by
    intro Lp Lq hl1 hl2
    rw [div_le_iff₀ hP]
    have hc := mul_le_mul_of_nonneg_left hcomb hP.le
    rcases le_total (A p + TP x0 + d * (p - x0)) (A q + TP x0 + d * (q - x0)) with hab | hab
    · rw [min_eq_left hab] at hc
      have := min_le_left (Lp : ℝ) Lq
      linarith
    · rw [min_eq_right hab] at hc
      have := min_le_right (Lp : ℝ) Lq
      linarith
  by_cases hxq : x0q = true
  · have hx0q : x0 = q := by rw [hx0def, if_pos hxq]
    have hz : (2 : ℝ) ^ P * (d * (q - x0)) = 0 := by rw [hx0q, sub_self, mul_zero, mul_zero]
    rw [if_pos hxq] at hsl
    simp only [hxq, if_true, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply hfin
    · simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hAp]
      linarith
    · simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hAq]
      linarith
  · have hx0p : x0 = p := by rw [hx0def, if_neg hxq]
    have hz : (2 : ℝ) ^ P * (d * (p - x0)) = 0 := by rw [hx0p, sub_self, mul_zero, mul_zero]
    rw [if_neg hxq] at hsl
    simp only [hxq, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply hfin
    · simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hAp]
      linarith
    · simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      rw [hAq]
      linarith
