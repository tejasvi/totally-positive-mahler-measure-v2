import AuxCommon.LogSound
import AuxCore.LogK

/-!
# Soundness of the table-reduced single-series logarithm `AuxCore.logK`

* `atanhK_fst`: the accumulated sum of `atanhK` is the floor-rounded sum `atanhLoAux` of `AuxCore.Log` (so the lower
  bound of `AuxCommon.LogSound` applies).
* `atanhK_pow_lower`, `atanhK_fst_lower`: the floor recursion loses at most `6` units per power and `7` per term.
* `logRatK_sound`: `(logRatK p J A B).1 ≤ 2^p log(A/B) ≤ (logRatK p J A B).2` for `0 < B ≤ A ≤ 2B`.
* `logK_sound`: for `a, b > 0` and valid enclosures of the table entries and of `log 2`, `logK` encloses `2^p log(a/b)`.
* `TableOK`, `tableCheck_sound`: the table hypothesis follows from a decidable comparison with `logRatK` at a higher
  precision (`tableCheck`), which the kernel evaluates once.
-/

namespace AuxCommon

open AuxCore Real

/-! ## The recursion -/

theorem atanhK_zero (p z2 j pw acc : ℕ) : atanhK p z2 0 j pw acc = (acc, pw) := rfl

theorem atanhK_succ (p z2 n j pw acc : ℕ) :
    atanhK p z2 (n + 1) j pw acc =
      atanhK p z2 n (j + 1) ((pw * z2) >>> p) (acc + pw / (2 * j + 1)) := rfl

theorem atanhK_fst (p z2 : ℕ) : ∀ (n j pw acc : ℕ),
    (atanhK p z2 n j pw acc).1 = acc + atanhLoAux p z2 n j pw := by
  intro n
  induction n with
  | zero => intro j pw acc; simp [atanhK_zero, atanhLoAux]
  | succ n ih =>
    intro j pw acc
    rw [atanhK_succ, ih]
    simp only [atanhLoAux]
    ring

/-- One step of the power recursion loses at most `6` units. -/
theorem pow_step_lower {p z2 pw j : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hz13 : z ≤ 1 / 3)
    (hz2lo : 2 ^ p * z ^ 2 - 3 ≤ (z2 : ℝ)) (hpw : 2 ^ p * z ^ (2 * j + 1) - 6 ≤ (pw : ℝ)) :
    2 ^ p * z ^ (2 * (j + 1) + 1) - 6 ≤ (((pw * z2) >>> p : ℕ) : ℝ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hfl : (pw : ℝ) * z2 / 2 ^ p - 1 ≤ (((pw * z2) >>> p : ℕ) : ℝ) := by
    rw [Nat.shiftRight_eq_div_pow]
    have h1 := Nat.lt_div_mul_add (a := pw * z2) (Nat.two_pow_pos p)
    have h2 : ((pw * z2 : ℕ) : ℝ) < (((pw * z2) / 2 ^ p : ℕ) : ℝ) * 2 ^ p + 2 ^ p := by exact_mod_cast h1
    push_cast at h2
    rw [sub_le_iff_le_add, div_le_iff₀ hp]
    linarith
  have hzpow : z ^ (2 * j + 1) ≤ 1 / 3 := by
    calc z ^ (2 * j + 1) ≤ z ^ 1 := pow_le_pow_of_le_one hz0 (by linarith) (by omega)
      _ = z := pow_one z
      _ ≤ 1 / 3 := hz13
  have hzz : z ^ (2 * (j + 1) + 1) = z ^ (2 * j + 1) * z ^ 2 := by ring
  by_cases hA : 6 ≤ 2 ^ p * z ^ (2 * j + 1)
  · by_cases hB : 3 ≤ 2 ^ p * z ^ 2
    · have hpw0 : 0 ≤ 2 ^ p * z ^ (2 * j + 1) - 6 := by linarith
      have hz20 : 0 ≤ 2 ^ p * z ^ 2 - 3 := by linarith
      have hprod : (2 ^ p * z ^ (2 * j + 1) - 6) * (2 ^ p * z ^ 2 - 3) ≤ (pw : ℝ) * z2 :=
        mul_le_mul hpw hz2lo hz20 (Nat.cast_nonneg _)
      have hkey : 2 ^ p * z ^ (2 * (j + 1) + 1) - 6 ≤ (pw : ℝ) * z2 / 2 ^ p - 1 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hp]
        have hz2sq : z ^ 2 ≤ 1 / 9 := by nlinarith
        set a := 2 ^ p * z ^ (2 * j + 1) with ha
        set b := 2 ^ p * z ^ 2 with hb
        have hab : (2 ^ p * z ^ (2 * (j + 1) + 1)) * 2 ^ p = a * b := by rw [ha, hb, hzz]; ring
        have ha3 : a ≤ 2 ^ p / 3 := by
          rw [ha]; have := mul_le_mul_of_nonneg_left hzpow hp.le; linarith
        have hb9 : b ≤ 2 ^ p / 9 := by
          rw [hb]; have := mul_le_mul_of_nonneg_left hz2sq hp.le; linarith
        have hexp : (a - 6) * (b - 3) = a * b - 3 * a - 6 * b + 18 := by ring
        rw [hexp] at hprod
        nlinarith [hab]
      linarith
    · have : 2 ^ p * z ^ (2 * (j + 1) + 1) - 6 < 0 := by
        rw [hzz]
        have h1 : 2 ^ p * (z ^ (2 * j + 1) * z ^ 2) = z ^ (2 * j + 1) * (2 ^ p * z ^ 2) := by ring
        rw [h1]
        have : z ^ (2 * j + 1) * (2 ^ p * z ^ 2) ≤ 1 / 3 * 3 := by
          apply mul_le_mul hzpow (by linarith) (by positivity) (by norm_num)
        linarith
      linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (((pw * z2) >>> p : ℕ) : ℝ))]
  · have : 2 ^ p * z ^ (2 * (j + 1) + 1) - 6 < 0 := by
      rw [hzz]
      have h1 : 2 ^ p * (z ^ (2 * j + 1) * z ^ 2) = (2 ^ p * z ^ (2 * j + 1)) * z ^ 2 := by ring
      rw [h1]
      have hz21 : z ^ 2 ≤ 1 := by nlinarith
      have : (2 ^ p * z ^ (2 * j + 1)) * z ^ 2 ≤ 2 ^ p * z ^ (2 * j + 1) :=
        mul_le_of_le_one_right (by positivity) hz21
      push Not at hA
      linarith
    linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (((pw * z2) >>> p : ℕ) : ℝ))]

/-- The final power of `atanhK` is at least `2^p z^(2(j+n)+1) - 6`. -/
theorem atanhK_pow_lower {p z2 : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hz13 : z ≤ 1 / 3)
    (hz2lo : 2 ^ p * z ^ 2 - 3 ≤ (z2 : ℝ)) :
    ∀ (n j pw acc : ℕ), 2 ^ p * z ^ (2 * j + 1) - 6 ≤ (pw : ℝ) →
      2 ^ p * z ^ (2 * (j + n) + 1) - 6 ≤ ((atanhK p z2 n j pw acc).2 : ℝ) := by
  intro n
  induction n with
  | zero => intro j pw acc h; simpa [atanhK_zero] using h
  | succ n ih =>
    intro j pw acc h
    rw [atanhK_succ]
    have := ih (j + 1) _ (acc + pw / (2 * j + 1)) (pow_step_lower hz0 hz13 hz2lo h)
    rwa [show j + 1 + n = j + (n + 1) by omega] at this

/-- The accumulated sum loses at most `7` units per term. -/
theorem atanhK_fst_lower {p z2 : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hz13 : z ≤ 1 / 3)
    (hz2lo : 2 ^ p * z ^ 2 - 3 ≤ (z2 : ℝ)) :
    ∀ (n j pw acc : ℕ), 2 ^ p * z ^ (2 * j + 1) - 6 ≤ (pw : ℝ) →
      (acc : ℝ) + 2 ^ p * ∑ i ∈ Finset.range n, aterm z (i + j) - 7 * n ≤ ((atanhK p z2 n j pw acc).1 : ℝ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  intro n
  induction n with
  | zero => intro j pw acc _; simp [atanhK_zero]
  | succ n ih =>
    intro j pw acc h
    rw [atanhK_succ]
    have hrec := ih (j + 1) _ (acc + pw / (2 * j + 1)) (pow_step_lower hz0 hz13 hz2lo h)
    have hterm : 2 ^ p * aterm z j - 7 ≤ ((pw / (2 * j + 1) : ℕ) : ℝ) := by
      have h1 := Nat.lt_div_mul_add (a := pw) (show 0 < 2 * j + 1 by omega)
      have h2 : (pw : ℝ) < ((pw / (2 * j + 1) : ℕ) : ℝ) * (2 * j + 1) + (2 * j + 1) := by exact_mod_cast h1
      have hd : (1 : ℝ) ≤ 2 * j + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
      unfold aterm
      have hq : (pw : ℝ) / (2 * j + 1) - 1 ≤ ((pw / (2 * j + 1) : ℕ) : ℝ) := by
        rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
        linarith
      have h3 : 2 ^ p * (z ^ (2 * j + 1) / (2 * j + 1)) - 6 / (2 * j + 1) ≤ (pw : ℝ) / (2 * j + 1) := by
        rw [mul_div_assoc', ← sub_div]
        exact div_le_div_of_nonneg_right h (by linarith)
      have h4 : 6 / (2 * (j : ℝ) + 1) ≤ 6 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      linarith
    have hsum : ∑ i ∈ Finset.range (n + 1), aterm z (i + j) =
        aterm z j + ∑ i ∈ Finset.range n, aterm z (i + (j + 1)) := by
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      · simp
      · apply Finset.sum_congr rfl; intro i _; congr 1; omega
    rw [hsum]
    push_cast at hrec ⊢
    nlinarith [hrec, hterm]

/-! ## `logRatK` -/

theorem logRatK_sound {p J A B : ℕ} (hB : 0 < B) (hBA : B ≤ A) (hA2 : A ≤ 2 * B) :
    ((logRatK p J A B).1 : ℝ) ≤ 2 ^ p * Real.log ((A : ℝ) / B) ∧
      2 ^ p * Real.log ((A : ℝ) / B) ≤ ((logRatK p J A B).2 : ℝ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hAB : (0 : ℝ) < (A : ℝ) + B := by positivity
  have hBA' : (B : ℝ) ≤ A := by exact_mod_cast hBA
  have hA2' : (A : ℝ) ≤ 2 * B := by exact_mod_cast hA2
  have hz0 : 0 ≤ ((A : ℝ) - B) / (A + B) := div_nonneg (by linarith) hAB.le
  have hz13 : ((A : ℝ) - B) / (A + B) ≤ 1 / 3 := by rw [div_le_iff₀ hAB]; linarith
  have hz1 : ((A : ℝ) - B) / (A + B) < 1 := by linarith
  have harg : (1 + ((A : ℝ) - B) / (A + B)) / (1 - ((A : ℝ) - B) / (A + B)) = (A : ℝ) / B := atanh_arg hB
  generalize hz : ((A : ℝ) - B) / (A + B) = z at hz0 hz13 hz1 harg
  -- the scaled argument
  have hzl_le : (((A - B) * 2 ^ p / (A + B) : ℕ) : ℝ) ≤ 2 ^ p * z := by
    refine (natCast_div_le' _ _).trans (le_of_eq ?_)
    rw [← hz, Nat.cast_mul, Nat.cast_sub hBA]; push_cast; ring
  have hzl_ge : 2 ^ p * z - 1 ≤ (((A - B) * 2 ^ p / (A + B) : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := (A - B) * 2 ^ p) (show 0 < A + B by omega)
    have h2 : (((A - B) * 2 ^ p : ℕ) : ℝ) < ((((A - B) * 2 ^ p) / (A + B) : ℕ) : ℝ) * ((A + B : ℕ) : ℝ) +
        ((A + B : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Nat.cast_mul, Nat.cast_sub hBA] at h2
    push_cast at h2
    rw [← hz, sub_le_iff_le_add, mul_div_assoc', div_le_iff₀ hAB]
    nlinarith
  set zl := (A - B) * 2 ^ p / (A + B) with hzl'
  have hz2_le : ((((zl * zl) >>> p) : ℕ) : ℝ) ≤ 2 ^ p * z ^ 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    refine (natCast_div_le' _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    calc (zl : ℝ) * zl ≤ (2 ^ p * z) * (2 ^ p * z) := mul_le_mul hzl_le hzl_le (Nat.cast_nonneg _) (by positivity)
      _ = 2 ^ p * z ^ 2 * 2 ^ p := by ring
  have hz2_ge : 2 ^ p * z ^ 2 - 3 ≤ ((((zl * zl) >>> p) : ℕ) : ℝ) := by
    rw [Nat.shiftRight_eq_div_pow]
    have h1 := Nat.lt_div_mul_add (a := zl * zl) (Nat.two_pow_pos p)
    have h2 : ((zl * zl : ℕ) : ℝ) < (((zl * zl) / 2 ^ p : ℕ) : ℝ) * 2 ^ p + 2 ^ p := by exact_mod_cast h1
    push_cast at h2
    by_cases hc : 0 ≤ 2 ^ p * z - 1
    · have hsq : (2 ^ p * z - 1) * (2 ^ p * z - 1) ≤ (zl : ℝ) * zl :=
        mul_le_mul hzl_ge hzl_ge hc (Nat.cast_nonneg _)
      have hpz : (2 ^ p : ℝ) * z ≤ 2 ^ p := by nlinarith
      have hp1 : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
      rw [sub_le_iff_le_add]
      have : 2 ^ p * z ^ 2 * 2 ^ p ≤ ((((zl * zl) / 2 ^ p : ℕ) : ℝ) + 3) * 2 ^ p := by nlinarith
      exact le_of_mul_le_mul_right this hp
    · have : 2 ^ p * z < 1 := by linarith
      have : 2 ^ p * z ^ 2 ≤ 1 := by
        have : 2 ^ p * z ^ 2 = (2 ^ p * z) * z := by ring
        rw [this]; nlinarith
      linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((((zl * zl) / 2 ^ p) : ℕ) : ℝ))]
  set z2 := (zl * zl) >>> p with hz2def
  have hval : logRatK p J A B =
      (2 * (atanhK p z2 J 0 zl 0).1,
        2 * ((atanhK p z2 J 0 zl 0).1 + 7 * J +
          (9 * ((atanhK p z2 J 0 zl 0).2 + 6) + (8 * (2 * J + 1) - 1)) / (8 * (2 * J + 1)))) := by
    rfl
  have hsum := hasSum_aterm hz0 hz1
  rw [harg] at hsum
  constructor
  · -- lower bound: the accumulated sum is the floor-rounded sum
    rw [hval]
    have h1 := atanhK_fst p z2 J 0 zl 0
    have h2 := atanhLoAux_le hz0 hz2_le J 0 zl (by simpa using hzl_le)
    have h3 : ∑ i ∈ Finset.range J, aterm z (i + 0) ≤ Real.log ((A : ℝ) / B) / 2 := by
      simpa using sum_le_hasSum (Finset.range J) (fun i _ => aterm_nonneg hz0 i) hsum
    simp only
    rw [h1]
    push_cast
    nlinarith
  · -- upper bound: rounding loss 7 per term, tail ≤ 9/8 of the next term
    rw [hval]
    have hpw : 2 ^ p * z ^ (2 * 0 + 1) - 6 ≤ (zl : ℝ) := by simp; linarith
    have hlow := atanhK_fst_lower hz0 hz13 hz2_ge J 0 zl 0 hpw
    have hpowJ := atanhK_pow_lower hz0 hz13 hz2_ge J 0 zl 0 hpw
    simp only [zero_add] at hpowJ
    have hsplit : Real.log ((A : ℝ) / B) / 2 =
        ∑ i ∈ Finset.range J, aterm z i + ∑' i : ℕ, aterm z (i + J) := by
      rw [← hsum.tsum_eq]
      exact (hsum.summable.sum_add_tsum_nat_add J).symm
    have htail := tsum_aterm_tail_le hz0 hz13 J
    set acc := (atanhK p z2 J 0 zl 0).1
    set pwJ := (atanhK p z2 J 0 zl 0).2
    have hceil := le_natCast_ceil_div (9 * (pwJ + 6)) (8 * (2 * J + 1)) (by omega)
    have hatJ : 2 ^ p * aterm z J ≤ ((pwJ : ℝ) + 6) / (2 * J + 1) := by
      unfold aterm
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    simp only [Finset.sum_congr rfl (fun i _ => show aterm z (i + 0) = aterm z i by simp)] at hlow
    have hfin : 2 ^ p * Real.log ((A : ℝ) / B) / 2 ≤
        (acc : ℝ) + 7 * J + 9 * ((pwJ : ℝ) + 6) / (8 * (2 * J + 1)) := by
      have e1 : 2 ^ p * Real.log ((A : ℝ) / B) / 2 =
          2 ^ p * ∑ i ∈ Finset.range J, aterm z i + 2 ^ p * ∑' i : ℕ, aterm z (i + J) := by
        rw [mul_div_assoc, hsplit, mul_add]
      have e2 : 2 ^ p * ∑' i : ℕ, aterm z (i + J) ≤ 9 * ((pwJ : ℝ) + 6) / (8 * (2 * J + 1)) := by
        calc 2 ^ p * ∑' i : ℕ, aterm z (i + J) ≤ 2 ^ p * (9 / 8 * aterm z J) :=
              mul_le_mul_of_nonneg_left htail hp.le
          _ = 9 / 8 * (2 ^ p * aterm z J) := by ring
          _ ≤ 9 / 8 * (((pwJ : ℝ) + 6) / (2 * J + 1)) := by
              apply mul_le_mul_of_nonneg_left hatJ (by norm_num)
          _ = 9 * ((pwJ : ℝ) + 6) / (8 * (2 * J + 1)) := by field_simp
      rw [e1]
      linarith
    have hc' : 9 * ((pwJ : ℝ) + 6) / (8 * (2 * J + 1)) ≤
        (((9 * (pwJ + 6) + (8 * (2 * J + 1) - 1)) / (8 * (2 * J + 1)) : ℕ) : ℝ) := by
      have := hceil
      push_cast at this ⊢
      exact this
    push_cast
    nlinarith

/-! ## `logK` -/

/-- Validity of the table: entry `i < 16` encloses `2^p log((16 + i)/16)`. -/
def TableOK (p T W : ℕ) : Prop :=
  ∀ i < 16, (fieldK T W (2 * i) : ℝ) ≤ 2 ^ p * Real.log ((16 + i : ℕ) / 16 : ℝ) ∧
    2 ^ p * Real.log ((16 + i : ℕ) / 16 : ℝ) ≤ fieldK T W (2 * i + 1)

/-- The decidable check behind `TableOK`: comparison with `logRatK` at precision `p + g`. -/
def tableCheck (p g J T W : ℕ) : Bool :=
  (List.range 16).all fun i =>
    let r := logRatK (p + g) J (16 + i) 16
    decide (fieldK T W (2 * i) * 2 ^ g ≤ r.1) && decide (r.2 ≤ fieldK T W (2 * i + 1) * 2 ^ g)

theorem tableCheck_sound {p g J T W : ℕ} (h : tableCheck p g J T W = true) : TableOK p T W := by
  intro i hi
  have hi' : i ∈ List.range 16 := List.mem_range.mpr hi
  have := List.all_eq_true.mp h i hi'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨hlo, hhi⟩ := this
  have hs := logRatK_sound (p := p + g) (J := J) (A := 16 + i) (B := 16) (by norm_num) (by omega) (by omega)
  have hpg : (2 : ℝ) ^ (p + g) = 2 ^ p * 2 ^ g := pow_add 2 p g
  have hg : (0 : ℝ) < 2 ^ g := by positivity
  have hlo' : ((fieldK T W (2 * i) : ℕ) : ℝ) * 2 ^ g ≤ ((logRatK (p + g) J (16 + i) 16).1 : ℝ) := by
    exact_mod_cast hlo
  have hhi' : ((logRatK (p + g) J (16 + i) 16).2 : ℝ) ≤ ((fieldK T W (2 * i + 1) : ℕ) : ℝ) * 2 ^ g := by
    exact_mod_cast hhi
  obtain ⟨hs1, hs2⟩ := hs
  rw [hpg] at hs1 hs2
  push_cast at hs1 hs2 ⊢
  constructor
  · have : (fieldK T W (2 * i) : ℝ) * 2 ^ g ≤ 2 ^ p * Real.log ((16 + i) / 16) * 2 ^ g := by nlinarith
    exact le_of_mul_le_mul_right this hg
  · have : 2 ^ p * Real.log ((16 + i) / 16) * 2 ^ g ≤ (fieldK T W (2 * i + 1) : ℝ) * 2 ^ g := by nlinarith
    exact le_of_mul_le_mul_right this hg

/-- The decidable check behind the `log 2` enclosure. -/
def l2Check (p g J l2lo l2hi : ℕ) : Bool :=
  let r := logRatK (p + g) J 2 1
  decide (l2lo * 2 ^ g ≤ r.1) && decide (r.2 ≤ l2hi * 2 ^ g)

theorem l2Check_sound {p g J l2lo l2hi : ℕ} (h : l2Check p g J l2lo l2hi = true) :
    (l2lo : ℝ) ≤ 2 ^ p * Real.log 2 ∧ 2 ^ p * Real.log 2 ≤ l2hi := by
  simp only [l2Check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlo, hhi⟩ := h
  have hs := logRatK_sound (p := p + g) (J := J) (A := 2) (B := 1) (by norm_num) (by norm_num) (by norm_num)
  have hpg : (2 : ℝ) ^ (p + g) = 2 ^ p * 2 ^ g := pow_add 2 p g
  have hg : (0 : ℝ) < 2 ^ g := by positivity
  have hlo' : (l2lo : ℝ) * 2 ^ g ≤ ((logRatK (p + g) J 2 1).1 : ℝ) := by exact_mod_cast hlo
  have hhi' : ((logRatK (p + g) J 2 1).2 : ℝ) ≤ (l2hi : ℝ) * 2 ^ g := by exact_mod_cast hhi
  obtain ⟨hs1, hs2⟩ := hs
  rw [hpg] at hs1 hs2
  norm_num at hs1 hs2
  constructor
  · have : (l2lo : ℝ) * 2 ^ g ≤ 2 ^ p * Real.log 2 * 2 ^ g := by nlinarith
    exact le_of_mul_le_mul_right this hg
  · have : 2 ^ p * Real.log 2 * 2 ^ g ≤ (l2hi : ℝ) * 2 ^ g := by nlinarith
    exact le_of_mul_le_mul_right this hg

/-- `A < 2B` for the reduction `logRed`. -/
theorem logRed_lt {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : (logRed a b).1 < 2 * (logRed a b).2.1 := by
  have hs1 : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le (by omega)
  have hs2 : a < 2 ^ (Nat.log2 a + 1) := Nat.lt_log2_self
  have ht1 : 2 ^ Nat.log2 b ≤ b := Nat.log2_self_le (by omega)
  have ht2 : b < 2 ^ (Nat.log2 b + 1) := Nat.lt_log2_self
  unfold logRed
  simp only [Nat.shiftLeft_eq, pow_one]
  generalize Nat.log2 a = s at *
  generalize Nat.log2 b = t at *
  have h2s : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2t : 0 < 2 ^ t := Nat.two_pow_pos t
  have hX2 : a * 2 ^ t < 2 * (2 ^ s * 2 ^ t) := by
    have := Nat.mul_lt_mul_of_pos_right hs2 h2t; rw [pow_succ] at this; linarith
  have hY1 : 2 ^ s * 2 ^ t ≤ b * 2 ^ s := by
    have := Nat.mul_le_mul_right (2 ^ s) ht1; linarith [Nat.mul_comm (2 ^ t) (2 ^ s)]
  split_ifs with h
  · dsimp only; omega
  · dsimp only; omega

/-- The core of `logK` after the reduction to `A / B ∈ [1, 2)`. -/
theorem logK_core {p J T W : ℕ} {l2lo l2hi : ℤ} {A B : ℕ} {e : ℤ} {x : ℝ} (hB : 0 < B) (hBA : B ≤ A)
    (hA2 : A < 2 * B) (hx : x = (2 : ℝ) ^ e * ((A : ℝ) / B)) (hT : TableOK p T W)
    (hl2lo : (l2lo : ℝ) ≤ 2 ^ p * Real.log 2) (hl2hi : 2 ^ p * Real.log 2 ≤ l2hi) :
    let i := Nat.div (Nat.mul 16 (Nat.sub A B)) B
    let r := logRatK p J (Nat.mul 16 A) (Nat.mul (Nat.add 16 i) B)
    let blo : ℤ := Int.ofNat (Nat.add r.1 (fieldK T W (Nat.mul 2 i)))
    let bhi : ℤ := Int.ofNat (Nat.add r.2 (fieldK T W (Nat.add (Nat.mul 2 i) 1)))
    let out : ℤ × ℤ := cond (Int.decLe 0 e).decide
      (Int.add blo (Int.mul e l2lo), Int.add bhi (Int.mul e l2hi))
      (Int.add blo (Int.mul e l2hi), Int.add bhi (Int.mul e l2lo))
    (out.1 : ℝ) ≤ 2 ^ p * Real.log x ∧ 2 ^ p * Real.log x ≤ (out.2 : ℝ) := by
  intro i r blo bhi out
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hA' : (0 : ℝ) < A := by have : 0 < A := lt_of_lt_of_le hB hBA; exact_mod_cast this
  have hi15 : i < 16 := by
    show 16 * (A - B) / B < 16
    rw [Nat.div_lt_iff_lt_mul hB]
    have : A - B < B := by omega
    omega
  have hiB : i * B ≤ 16 * (A - B) := Nat.div_mul_le_self _ _
  have h1 : (16 + i) * B ≤ 16 * A := by
    have : 16 * (A - B) + 16 * B = 16 * A := by rw [← Nat.mul_add, Nat.sub_add_cancel hBA]
    nlinarith
  have h2 : 16 * A ≤ 2 * ((16 + i) * B) := by nlinarith
  have hB2 : 0 < (16 + i) * B := by positivity
  have hr := logRatK_sound (p := p) (J := J) hB2 h1 h2
  obtain ⟨htlo, hthi⟩ := hT i hi15
  have hi' : (0 : ℝ) < 16 + (i : ℝ) := by positivity
  have hlogAB : Real.log ((A : ℝ) / B) = Real.log ((16 + i : ℕ) / 16 : ℝ) +
      Real.log (((16 * A : ℕ) : ℝ) / ((16 + i) * B : ℕ)) := by
    have hA0 : 0 < A := lt_of_lt_of_le hB hBA
    have hpos1 : (0 : ℝ) < ((16 + i : ℕ) : ℝ) / 16 := by positivity
    have hpos2 : (0 : ℝ) < ((16 * A : ℕ) : ℝ) / ((16 + i) * B : ℕ) := by
      apply div_pos <;> exact_mod_cast (by positivity)
    rw [← Real.log_mul hpos1.ne' hpos2.ne']
    congr 1
    push_cast
    have h16 : (16 : ℝ) + i ≠ 0 := hi'.ne'
    have hBne : (B : ℝ) ≠ 0 := hB'.ne'
    field_simp
  have hlog : Real.log x = e * Real.log 2 + Real.log ((A : ℝ) / B) := by
    rw [hx, Real.log_mul (by positivity) (by positivity), Real.log_zpow]
  rw [hlog, hlogAB]
  obtain ⟨hr1, hr2⟩ := hr
  have hr1' : ((r.1 : ℕ) : ℝ) ≤ 2 ^ p * Real.log (((16 * A : ℕ) : ℝ) / ((16 + i) * B : ℕ)) := hr1
  have hr2' : 2 ^ p * Real.log (((16 * A : ℕ) : ℝ) / ((16 + i) * B : ℕ)) ≤ ((r.2 : ℕ) : ℝ) := hr2
  have hblo : (blo : ℝ) = (r.1 : ℝ) + (fieldK T W (2 * i) : ℝ) := by
    show ((Int.ofNat (r.1 + fieldK T W (2 * i)) : ℤ) : ℝ) = _
    rw [Int.ofNat_eq_natCast]; push_cast; ring
  have hbhi : (bhi : ℝ) = (r.2 : ℝ) + (fieldK T W (2 * i + 1) : ℝ) := by
    show ((Int.ofNat (r.2 + fieldK T W (2 * i + 1)) : ℤ) : ℝ) = _
    rw [Int.ofNat_eq_natCast]; push_cast; ring
  by_cases he : 0 ≤ e
  · have hout : out = (blo + e * l2lo, bhi + e * l2hi) := by
      show cond (Int.decLe 0 e).decide _ _ = _
      rw [show (Int.decLe 0 e).decide = true from decide_eq_true he]; rfl
    have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    rw [hout]
    simp only
    push_cast at htlo hthi hr1' hr2' ⊢
    rw [hblo, hbhi]
    have m1 := mul_le_mul_of_nonneg_left hl2lo he'
    have m2 := mul_le_mul_of_nonneg_left hl2hi he'
    constructor <;> nlinarith
  · have hout : out = (blo + e * l2hi, bhi + e * l2lo) := by
      show cond (Int.decLe 0 e).decide _ _ = _
      rw [show (Int.decLe 0 e).decide = false from decide_eq_false he]; rfl
    have he' : (e : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge he)
    rw [hout]
    simp only
    push_cast at htlo hthi hr1' hr2' ⊢
    rw [hblo, hbhi]
    have m1 := mul_le_mul_of_nonpos_left hl2hi he'.le
    have m2 := mul_le_mul_of_nonpos_left hl2lo he'.le
    constructor <;> nlinarith

/-- **Soundness of `logK`.** -/
theorem logK_sound {p J T W : ℕ} {l2lo l2hi : ℤ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hT : TableOK p T W) (hl2lo : (l2lo : ℝ) ≤ 2 ^ p * Real.log 2) (hl2hi : 2 ^ p * Real.log 2 ≤ l2hi) :
    ((logK p J T W l2lo l2hi a b).1 : ℝ) ≤ 2 ^ p * Real.log ((a : ℝ) / b) ∧
      2 ^ p * Real.log ((a : ℝ) / b) ≤ ((logK p J T W l2lo l2hi a b).2 : ℝ) := by
  obtain ⟨hB, hBA, _, heq⟩ := logRed_spec ha hb
  have hlt := logRed_lt ha hb
  have hcore := logK_core (p := p) (J := J) (T := T) (W := W) (l2lo := l2lo) (l2hi := l2hi) hB hBA hlt heq hT
    hl2lo hl2hi
  -- `logK` computes exactly `logK_core`'s expression for `(A, B, e) = logRed a b`
  have hsame : logK p J T W l2lo l2hi a b =
      (let A := (logRed a b).1
       let B := (logRed a b).2.1
       let e := (logRed a b).2.2
       let i := Nat.div (Nat.mul 16 (Nat.sub A B)) B
       let r := logRatK p J (Nat.mul 16 A) (Nat.mul (Nat.add 16 i) B)
       let blo : ℤ := Int.ofNat (Nat.add r.1 (fieldK T W (Nat.mul 2 i)))
       let bhi : ℤ := Int.ofNat (Nat.add r.2 (fieldK T W (Nat.add (Nat.mul 2 i) 1)))
       cond (Int.decLe 0 e).decide
         (Int.add blo (Int.mul e l2lo), Int.add bhi (Int.mul e l2hi))
         (Int.add blo (Int.mul e l2hi), Int.add bhi (Int.mul e l2lo))) := by
    unfold logK logRed
    dsimp only
    by_cases hc : b <<< Nat.log2 a ≤ a <<< Nat.log2 b
    · have hb : Nat.ble (Nat.shiftLeft b (Nat.log2 a)) (Nat.shiftLeft a (Nat.log2 b)) = true := Nat.ble_eq.mpr hc
      simp only [hb, Bool.cond_true, if_pos hc, Int.subNatNat_eq_coe]
      rfl
    · have hb : Nat.ble (Nat.shiftLeft b (Nat.log2 a)) (Nat.shiftLeft a (Nat.log2 b)) = false := by
        rw [Bool.eq_false_iff]; intro h; exact hc (Nat.ble_eq.mp h)
      simp only [hb, Bool.cond_false, if_neg hc, Int.subNatNat_eq_coe]
      have he : ((Nat.log2 a : ℕ) : ℤ) - ((Nat.add (Nat.log2 b) 1 : ℕ) : ℤ) =
          (Nat.log2 a : ℤ) - (Nat.log2 b : ℤ) - 1 := by
        show ((Nat.log2 a : ℕ) : ℤ) - ((Nat.log2 b + 1 : ℕ) : ℤ) = _
        push_cast; ring
      rw [he]
      rfl
  rw [hsame]
  exact hcore

end AuxCommon
