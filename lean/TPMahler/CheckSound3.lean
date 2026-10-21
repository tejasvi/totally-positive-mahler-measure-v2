import TPMahler.CheckSound2

/-!
# Soundness of the checker, part 3: the node pass of a chord leaf (`leafPass`)

For a chord leaf `[p, q] = [Xp / D, Xq / D]` the node pass returns enclosures of the potential at `p` and at `q` without
the singular terms (`C_i > 0` and `e_i ∈ {p, q}`), an upper bound for the node part of the curvature, and a flag for a node
(with `C_i ≠ 0`) strictly inside `(p, q)`.
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-- Node `i` is singular at the leaf `[p, q]`: `C_i > 0` and `e_i ∈ {p, q}`. -/
def singI (k Xp Xq i : ℕ) : Prop :=
  0 < CR i ∧ (nodes.getD i 0 * 2 ^ k = Xp ∨ nodes.getD i 0 * 2 ^ k = Xq)

noncomputable instance (k Xp Xq i : ℕ) : Decidable (singI k Xp Xq i) := by unfold singI; infer_instance

/-- The bracket of `log |x - e|` between the end points. -/
theorem abs_between {e p q x : ℝ} (hx1 : p < x) (hx2 : x < q) (hout : ¬ (p < e ∧ e < q)) (hep : e ≠ p)
    (heq : e ≠ q) : min |p - e| |q - e| ≤ |x - e| ∧ |x - e| ≤ max |p - e| |q - e| ∧ 0 < |x - e| := by
  by_cases h : e < p
  · have h1 : |p - e| = p - e := abs_of_pos (by linarith)
    have h2 : |q - e| = q - e := abs_of_pos (by linarith)
    have h3 : |x - e| = x - e := abs_of_pos (by linarith)
    rw [h1, h2, h3]
    refine ⟨min_le_of_left_le (by linarith), le_max_of_le_right (by linarith), by linarith⟩
  · have hq : q < e := by
      by_contra hc
      push Not at h hc
      exact hout ⟨lt_of_le_of_ne h (Ne.symm hep), lt_of_le_of_ne hc heq⟩
    have h1 : |p - e| = e - p := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    have h2 : |q - e| = e - q := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    have h3 : |x - e| = e - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
    rw [h1, h2, h3]
    refine ⟨min_le_of_right_le (by linarith), le_max_of_le_left (by linarith), by linarith⟩

/-- The contributions of one node to the accumulator of a chord leaf. -/
theorem leafStep_spec {k Xp Xq i : ℕ} (hi : i ≤ NN) (hpq : Xp < Xq) {LD : ℤ × ℤ}
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ∧ 2 ^ P * Real.log (DEC * 2 ^ k : ℕ) ≤ LD.2)
    (a : LAcc) :
    let D : ℕ := DEC * 2 ^ k
    let p : ℝ := Xp / D
    let q : ℝ := Xq / D
    let a' := leafStep TAB L2 k Xp Xq LD a (recOf i)
    (a'.inside = false → a.inside = false) ∧
    (a'.inside = false →
      (CR i ≠ 0 → ¬ (p < eR i ∧ eR i < q)) ∧
      ((a'.spl : ℝ) - a.spl ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ∧
        4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (if singI k Xp Xq i then 0 else CR i * Hk (eR i - p)) ≤ (a'.sph : ℝ) - a.sph) ∧
      ((a'.sql : ℝ) - a.sql ≤ 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ∧
        4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (if singI k Xp Xq i then 0 else CR i * Hk (eR i - q)) ≤ (a'.sqh : ℝ) - a.sqh) ∧
      (∀ x : ℝ, p < x → x < q →
        2 ^ (P + QS) * (if singI k Xp Xq i then 0 else -2 * CR i * Real.log |x - eR i|) ≤ (a'.m : ℝ) - a.m)) := by
  intro D p q a'
  obtain ⟨hclo, hchi, hsg0, hsgpos, hn⟩ := recOf_spec hi
  have hD : 0 < D := Nat.mul_pos (by decide) (Nat.two_pow_pos k)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hPQ : (2 : ℝ) ^ (P + QS) = 2 ^ P * 2 ^ QS := pow_add 2 P QS
  have hQ : (0 : ℝ) < 2 ^ QS := by positivity
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  set ni : ℕ := nodes.getD i 0 * 2 ^ k with hni
  -- real positions
  have hep : eR i - p = ((nodes.getD i 0 : ℝ) * 2 ^ k - Xp) / D := eR_sub_x i k Xp
  have heq : eR i - q = ((nodes.getD i 0 : ℝ) * 2 ^ k - Xq) / D := eR_sub_x i k Xq
  have hniR : (ni : ℝ) = (nodes.getD i 0 : ℝ) * 2 ^ k := by rw [hni]; push_cast; ring
  by_cases hs : (recOf i).sg = 0
  · -- `C_i = 0`: nothing changes
    have hC : CR i = 0 := hsg0.mp hs
    have ha' : a' = a := by simp only [a', leafStep, hs, if_true]
    rw [ha']
    refine ⟨id, fun _ => ⟨fun h => absurd hC h, ?_, ?_, ?_⟩⟩
    · simp [hC]
    · simp [hC]
    · intro x _ _; simp [hC]
  · have hC : CR i ≠ 0 := fun h => hs (hsg0.mpr h)
    by_cases hin : Xp < ni ∧ ni < Xq
    · -- a node strictly inside: the flag is set
      have ha' : a'.inside = true := by
        simp only [a', leafStep, hs, if_false, hn, ← hni, if_pos hin]
      refine ⟨fun h => by rw [ha'] at h; exact absurd h (by simp), fun h => by rw [ha'] at h; exact absurd h (by simp)⟩
    · have hnotin : ¬ (p < eR i ∧ eR i < q) := by
        intro ⟨h1, h2⟩
        apply hin
        have h1' : (Xp : ℝ) < ni := by
          have : 0 < eR i - p := by linarith
          rw [hep] at this
          have := (div_pos_iff_of_pos_right hDR).mp this
          linarith
        have h2' : (ni : ℝ) < Xq := by
          have : eR i - q < 0 := by linarith
          rw [heq] at this
          have := (div_neg_iff.mp this)
          rcases this with ⟨_, h⟩ | ⟨h, _⟩
          · linarith
          · linarith
        exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
      set ap : ℕ := if Xp ≤ ni then ni - Xp else Xp - ni with hap
      set aq : ℕ := if Xq ≤ ni then ni - Xq else Xq - ni with haq
      have hapR : (ap : ℝ) = |(nodes.getD i 0 : ℝ) * 2 ^ k - Xp| := dist_cast _ _ _
      have haqR : (aq : ℝ) = |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| := dist_cast _ _ _
      have hsingI : singI k Xp Xq i ↔ (0 < (recOf i).sg ∧ (ap = 0 ∨ aq = 0)) := by
        unfold singI
        rw [hsgpos]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | h2
          · left; rw [hap]; rw [← hni] at h2; split_ifs <;> omega
          · right; rw [haq]; rw [← hni] at h2; split_ifs <;> omega
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases h2 with h2 | h2
          · left; rw [← hni]; rw [hap] at h2; split_ifs at h2 <;> omega
          · right; rw [← hni]; rw [haq] at h2; split_ifs at h2 <;> omega
      by_cases hsg : 0 < (recOf i).sg ∧ (ap = 0 ∨ aq = 0)
      · -- singular: nothing changes
        have hsI : singI k Xp Xq i := hsingI.mpr hsg
        have ha' : a' = a := by
          simp only [a', leafStep, hs, if_false, hn, ← hni, if_neg hin, ← hap, ← haq]
          have : (decide (0 < (recOf i).sg) && (ap == 0 || aq == 0)) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]; exact hsg
          rw [if_pos this]
        rw [ha']
        refine ⟨id, fun _ => ⟨fun _ => hnotin, ?_, ?_, ?_⟩⟩
        · simp [hsI]
        · simp [hsI]
        · intro x _ _; simp [hsI]
      · have hnsI : ¬ singI k Xp Xq i := fun h => hsg (hsingI.mp h)
        set Lp := logT TAB L2 ap 1 with hLp
        set Lq := logT TAB L2 aq 1 with hLq
        have ha' : a' = ⟨a.spl + (if ap = 0 then ((0 : ℤ), (0 : ℤ)) else imul ((recOf i).clo, (recOf i).chi)
              (yEncl ap Lp LD)).1,
            a.sph + (if ap = 0 then ((0 : ℤ), (0 : ℤ)) else imul ((recOf i).clo, (recOf i).chi) (yEncl ap Lp LD)).2,
            a.sql + (if aq = 0 then ((0 : ℤ), (0 : ℤ)) else imul ((recOf i).clo, (recOf i).chi) (yEncl aq Lq LD)).1,
            a.sqh + (if aq = 0 then ((0 : ℤ), (0 : ℤ)) else imul ((recOf i).clo, (recOf i).chi) (yEncl aq Lq LD)).2,
            a.m + (if 0 < (recOf i).sg then
                -2 * (if 0 ≤ min Lp.1 Lq.1 - LD.2 then (recOf i).clo * (min Lp.1 Lq.1 - LD.2)
                      else (recOf i).chi * (min Lp.1 Lq.1 - LD.2))
              else 2 * (if 0 ≤ (if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1
                        then (-(recOf i).clo) * ((if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1)
                        else (-(recOf i).chi) * ((if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1))),
            a.inside⟩ := by
          simp only [a', leafStep, hs, if_false, hn, ← hni, if_neg hin, ← hap, ← haq, ← hLp, ← hLq]
          have : (decide (0 < (recOf i).sg) && (ap == 0 || aq == 0)) = false := by
            rw [Bool.eq_false_iff]
            simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
            exact hsg
          rw [if_neg (by rw [this]; simp)]
        rw [ha']
        refine ⟨id, fun _ => ⟨fun _ => hnotin, ?_, ?_, ?_⟩⟩
        · -- potential at p
          simp only [if_neg hnsI]
          by_cases hap0 : ap = 0
          · have h0 : (nodes.getD i 0 : ℝ) * 2 ^ k - Xp = 0 := by
              have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xp| = 0 := by rw [← hapR, hap0]; simp
              exact abs_eq_zero.mp this
            simp only [hap0, if_true]
            rw [hep, h0]; simp [Hk]
          · simp only [hap0, if_false]
            have hpos : 0 < ap := Nat.pos_of_ne_zero hap0
            have habs : |eR i - p| = ap / D := by rw [hep, abs_div, abs_of_pos hDR, hapR]
            have hy := yEncl_spec hpos hD hLD habs
            have hm := imul_spec (a := ((recOf i).clo, (recOf i).chi)) ⟨hclo, hchi⟩ hy
            have e1 : 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (CR i * Hk (eR i - p)) =
                (2 ^ QS * CR i) * (4 * 2 ^ P * (D : ℝ) ^ 2 * Hk (eR i - p)) := by rw [hPQ]; ring
            rw [e1]; push_cast
            constructor <;> linarith [hm.1, hm.2]
        · -- potential at q
          simp only [if_neg hnsI]
          by_cases haq0 : aq = 0
          · have h0 : (nodes.getD i 0 : ℝ) * 2 ^ k - Xq = 0 := by
              have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| = 0 := by rw [← haqR, haq0]; simp
              exact abs_eq_zero.mp this
            simp only [haq0, if_true]
            rw [heq, h0]; simp [Hk]
          · simp only [haq0, if_false]
            have hpos : 0 < aq := Nat.pos_of_ne_zero haq0
            have habs : |eR i - q| = aq / D := by rw [heq, abs_div, abs_of_pos hDR, haqR]
            have hy := yEncl_spec hpos hD hLD habs
            have hm := imul_spec (a := ((recOf i).clo, (recOf i).chi)) ⟨hclo, hchi⟩ hy
            have e1 : 4 * 2 ^ (P + QS) * (D : ℝ) ^ 2 * (CR i * Hk (eR i - q)) =
                (2 ^ QS * CR i) * (4 * 2 ^ P * (D : ℝ) ^ 2 * Hk (eR i - q)) := by rw [hPQ]; ring
            rw [e1]; push_cast
            constructor <;> linarith [hm.1, hm.2]
        · -- curvature
          intro x hx1 hx2
          simp only [if_neg hnsI]
          have hpq' : p < q := by
            show (Xp : ℝ) / D < (Xq : ℝ) / D
            exact div_lt_div_of_pos_right (by exact_mod_cast hpq) hDR
          -- logs at the end points
          have hlogp : ∀ hap0 : ap ≠ 0, (Lp.1 : ℝ) - LD.2 ≤ 2 ^ P * Real.log |p - eR i| ∧
              2 ^ P * Real.log |p - eR i| ≤ (Lp.2 : ℝ) - LD.1 := by
            intro hap0
            have hpos : 0 < ap := Nat.pos_of_ne_zero hap0
            obtain ⟨h1, h2⟩ := logT_sound (a := ap) (b := 1) hpos one_pos
            simp only [Nat.cast_one, div_one] at h1 h2
            have habs : |p - eR i| = ap / D := by rw [abs_sub_comm, hep, abs_div, abs_of_pos hDR, hapR]
            rw [habs, Real.log_div (by exact_mod_cast hpos.ne') hDR.ne', mul_sub]
            constructor <;> linarith [hLD.1, hLD.2]
          have hlogq : ∀ haq0 : aq ≠ 0, (Lq.1 : ℝ) - LD.2 ≤ 2 ^ P * Real.log |q - eR i| ∧
              2 ^ P * Real.log |q - eR i| ≤ (Lq.2 : ℝ) - LD.1 := by
            intro haq0
            have hpos : 0 < aq := Nat.pos_of_ne_zero haq0
            obtain ⟨h1, h2⟩ := logT_sound (a := aq) (b := 1) hpos one_pos
            simp only [Nat.cast_one, div_one] at h1 h2
            have habs : |q - eR i| = aq / D := by rw [abs_sub_comm, heq, abs_div, abs_of_pos hDR, haqR]
            rw [habs, Real.log_div (by exact_mod_cast hpos.ne') hDR.ne', mul_sub]
            constructor <;> linarith [hLD.1, hLD.2]
          set vlo : ℤ := min Lp.1 Lq.1 - LD.2 with hvlo
          set vhi : ℤ := (if ap = 0 then Lq.2 else if aq = 0 then Lp.2 else max Lp.2 Lq.2) - LD.1 with hvhi
          set L : ℝ := Real.log |x - eR i| with hL
          by_cases hpos : 0 < (recOf i).sg
          · -- `C_i > 0`: both distances are positive (not singular), bracket from below
            have hap0 : ap ≠ 0 := fun h => hsg ⟨hpos, Or.inl h⟩
            have haq0 : aq ≠ 0 := fun h => hsg ⟨hpos, Or.inr h⟩
            have hCpos : 0 < CR i := hsgpos.mp hpos
            have hep' : eR i ≠ p := by
              intro h; apply hap0
              have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xp| = 0 := by
                rw [abs_eq_zero]
                have : eR i - p = 0 := by rw [h]; ring
                rw [hep] at this
                exact (div_eq_zero_iff.mp this).resolve_right hDR.ne'
              rw [← hapR] at this; exact_mod_cast this
            have heq' : eR i ≠ q := by
              intro h; apply haq0
              have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| = 0 := by
                rw [abs_eq_zero]
                have : eR i - q = 0 := by rw [h]; ring
                rw [heq] at this
                exact (div_eq_zero_iff.mp this).resolve_right hDR.ne'
              rw [← haqR] at this; exact_mod_cast this
            obtain ⟨hb1, hb2, hb3⟩ := abs_between hx1 hx2 hnotin hep' heq'
            have hLlo : (vlo : ℝ) ≤ 2 ^ P * L := by
              have hmin : Real.log (min |p - eR i| |q - eR i|) ≤ L := by
                apply Real.log_le_log (lt_min (abs_pos.mpr (sub_ne_zero.mpr hep'.symm))
                  (abs_pos.mpr (sub_ne_zero.mpr heq'.symm))) hb1
              rw [abs_sub_comm x] at hb1 hb2 hb3
              have h1 := (hlogp hap0).1
              have h2 := (hlogq haq0).1
              rw [hvlo]; push_cast
              rcases le_total |p - eR i| |q - eR i| with hle | hle
              · rw [min_eq_left hle] at hmin
                have := mul_le_mul_of_nonneg_left hmin hP.le
                have hm : (min (Lp.1 : ℝ) (Lq.1 : ℝ)) ≤ Lp.1 := min_le_left _ _
                linarith
              · rw [min_eq_right hle] at hmin
                have := mul_le_mul_of_nonneg_left hmin hP.le
                have hm : (min (Lp.1 : ℝ) (Lq.1 : ℝ)) ≤ Lq.1 := min_le_right _ _
                linarith
            simp only [hpos, if_true]
            have hclo0 : (0 : ℝ) ≤ (recOf i).clo := by
              have := (recOf i).clo
              by_contra hneg; push Not at hneg
              -- clo = ⌊2^QS C⌋ ≥ 0 since C > 0
              have hcl : ((recOf i).clo : ℝ) ≤ 2 ^ QS * CR i := hclo
              have : (recOf i).clo < 0 := by exact_mod_cast hneg
              have hfl : (recOf i).clo = fdiv (recNum i * 2 ^ QS) (recDen i) := rfl
              have hnum : 0 < recNum i := by
                have := hsgpos.mpr hCpos
                exact Int.sign_pos_iff.mp this
              have hfd : fdiv (recNum i * 2 ^ QS) (recDen i) = (recNum i * 2 ^ QS) / ((recDen i : ℕ) : ℤ) := rfl
              have : 0 ≤ fdiv (recNum i * 2 ^ QS) (recDen i) := by
                rw [hfd]
                exact Int.ediv_nonneg (by have : (0 : ℤ) < 2 ^ QS := by positivity
                                          nlinarith) (by positivity)
              omega
            have e1 : (2 : ℝ) ^ (P + QS) * (-2 * CR i * L) = -2 * ((2 ^ QS * CR i) * (2 ^ P * L)) := by
              rw [hPQ]; ring
            rw [e1]
            push_cast
            split_ifs with hv
            · have hv' : (0 : ℝ) ≤ vlo := by exact_mod_cast hv
              have : ((recOf i).clo : ℝ) * vlo ≤ (2 ^ QS * CR i) * (2 ^ P * L) :=
                mul_le_mul hclo hLlo hv' (mul_pos hQ hCpos).le
              linarith
            · have hv' : (vlo : ℝ) < 0 := by push Not at hv; exact_mod_cast hv
              have h1 : (2 ^ QS * CR i) * (vlo : ℝ) ≤ (2 ^ QS * CR i) * (2 ^ P * L) :=
                mul_le_mul_of_nonneg_left hLlo (mul_pos hQ hCpos).le
              have h2 : ((recOf i).chi : ℝ) * vlo ≤ (2 ^ QS * CR i) * vlo :=
                mul_le_mul_of_nonpos_right hchi hv'.le
              linarith
          · -- `C_i < 0`: bracket from above
            have hCneg : CR i < 0 := by
              rcases lt_trichotomy (CR i) 0 with h | h | h
              · exact h
              · exact absurd h hC
              · exact absurd (hsgpos.mpr h) hpos
            have hLhi : 2 ^ P * L ≤ (vhi : ℝ) := by
              rw [hvhi]
              by_cases hap0 : ap = 0
              · -- `e_i = p`: `log |x - e_i| ≤ log (q - p) = log |q - e_i|`
                have hep' : eR i = p := by
                  have h0 : (nodes.getD i 0 : ℝ) * 2 ^ k - Xp = 0 := by
                    have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xp| = 0 := by rw [← hapR, hap0]; simp
                    exact abs_eq_zero.mp this
                  have : eR i - p = 0 := by rw [hep, h0]; simp
                  linarith
                have haq0 : aq ≠ 0 := by
                  intro h
                  have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| = 0 := by rw [← haqR, h]; simp
                  have h0 := abs_eq_zero.mp this
                  have : eR i - q = 0 := by rw [heq, h0]; simp
                  linarith
                simp only [hap0, if_true]
                have h2 := (hlogq haq0).2
                have hle : L ≤ Real.log |q - eR i| := by
                  apply Real.log_le_log
                  · rw [hep']; exact abs_pos.mpr (by linarith)
                  · rw [hep', abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
                have := mul_le_mul_of_nonneg_left hle hP.le
                push_cast; linarith
              · by_cases haq0 : aq = 0
                · have heq' : eR i = q := by
                    have h0 : (nodes.getD i 0 : ℝ) * 2 ^ k - Xq = 0 := by
                      have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| = 0 := by rw [← haqR, haq0]; simp
                      exact abs_eq_zero.mp this
                    have : eR i - q = 0 := by rw [heq, h0]; simp
                    linarith
                  simp only [hap0, if_false, haq0, if_true]
                  have h2 := (hlogp hap0).2
                  have hle : L ≤ Real.log |p - eR i| := by
                    apply Real.log_le_log
                    · rw [heq']; exact abs_pos.mpr (by linarith)
                    · rw [heq', abs_of_neg (by linarith), abs_of_neg (by linarith)]; linarith
                  have := mul_le_mul_of_nonneg_left hle hP.le
                  push_cast; linarith
                · simp only [hap0, if_false, haq0]
                  have hep' : eR i ≠ p := by
                    intro h
                    apply hap0
                    have : eR i - p = 0 := by rw [h]; ring
                    rw [hep] at this
                    have h0 := (div_eq_zero_iff.mp this).resolve_right hDR.ne'
                    have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xp| = 0 := by rw [h0]; simp
                    rw [← hapR] at this; exact_mod_cast this
                  have heq' : eR i ≠ q := by
                    intro h
                    apply haq0
                    have : eR i - q = 0 := by rw [h]; ring
                    rw [heq] at this
                    have h0 := (div_eq_zero_iff.mp this).resolve_right hDR.ne'
                    have : |(nodes.getD i 0 : ℝ) * 2 ^ k - Xq| = 0 := by rw [h0]; simp
                    rw [← haqR] at this; exact_mod_cast this
                  obtain ⟨hb1, hb2, hb3⟩ := abs_between hx1 hx2 hnotin hep' heq'
                  rw [abs_sub_comm x] at hb1 hb2 hb3
                  have hmax : L ≤ Real.log (max |p - eR i| |q - eR i|) := by
                    rw [hL, abs_sub_comm]
                    exact Real.log_le_log hb3 hb2
                  have h1 := (hlogp hap0).2
                  have h2 := (hlogq haq0).2
                  push_cast
                  rcases le_total |p - eR i| |q - eR i| with hle | hle
                  · rw [max_eq_right hle] at hmax
                    have := mul_le_mul_of_nonneg_left hmax hP.le
                    have hm : (Lq.2 : ℝ) ≤ max (Lp.2 : ℝ) (Lq.2 : ℝ) := le_max_right _ _
                    linarith
                  · rw [max_eq_left hle] at hmax
                    have := mul_le_mul_of_nonneg_left hmax hP.le
                    have hm : (Lp.2 : ℝ) ≤ max (Lp.2 : ℝ) (Lq.2 : ℝ) := le_max_left _ _
                    linarith
            simp only [hpos, if_false]
            have hchi0 : ((recOf i).chi : ℝ) ≤ 0 := by
              have hnum : recNum i < 0 := by
                have h1 : ¬ 0 < Int.sign (recNum i) := hpos
                have h2 : Int.sign (recNum i) ≠ 0 := hs
                rcases Int.sign_trichotomy (recNum i) with h | h | h
                · exact absurd (by rw [h]; norm_num) h1
                · exact absurd h h2
                · exact Int.sign_eq_neg_one_iff_neg.mp h
              have hcd : cdiv (recNum i * 2 ^ QS) (recDen i) =
                  -((-(recNum i * 2 ^ QS)) / ((recDen i : ℕ) : ℤ)) := rfl
              have : cdiv (recNum i * 2 ^ QS) (recDen i) ≤ 0 := by
                rw [hcd]
                have h2p : (0 : ℤ) < 2 ^ QS := by positivity
                have : 0 ≤ (-(recNum i * 2 ^ QS)) / ((recDen i : ℕ) : ℤ) :=
                  Int.ediv_nonneg (by nlinarith) (by positivity)
                omega
              exact_mod_cast this
            have e1 : (2 : ℝ) ^ (P + QS) * (-2 * CR i * L) = 2 * ((-(2 ^ QS * CR i)) * (2 ^ P * L)) := by
              rw [hPQ]; ring
            rw [e1]
            push_cast
            have hCq : 0 ≤ -(2 ^ QS * CR i) := by nlinarith
            split_ifs with hv
            · have hv' : (0 : ℝ) ≤ vhi := by exact_mod_cast hv
              -- `-(2^QS C) ≤ -clo`
              have hb : -(2 ^ QS * CR i) ≤ -((recOf i).clo : ℝ) := by linarith
              rcases le_total 0 (2 ^ P * L) with hL0 | hL0
              · have : (-(2 ^ QS * CR i)) * (2 ^ P * L) ≤ (-((recOf i).clo : ℝ)) * vhi :=
                  mul_le_mul hb hLhi hL0 (by linarith)
                linarith
              · have h1 : (-(2 ^ QS * CR i)) * (2 ^ P * L) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hCq hL0
                have h2 : 0 ≤ (-((recOf i).clo : ℝ)) * vhi := mul_nonneg (by linarith) hv'
                linarith
            · have hv' : (vhi : ℝ) < 0 := by push Not at hv; exact_mod_cast hv
              have h1 : (-(2 ^ QS * CR i)) * (2 ^ P * L) ≤ (-(2 ^ QS * CR i)) * vhi :=
                mul_le_mul_of_nonneg_left hLhi hCq
              have h2 : (-(2 ^ QS * CR i)) * (vhi : ℝ) ≤ (-((recOf i).chi : ℝ)) * vhi :=
                mul_le_mul_of_nonpos_right (by linarith) hv'.le
              linarith

end TPMahler.Cert
