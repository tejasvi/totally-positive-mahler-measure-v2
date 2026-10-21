import Mathlib
import AuxCore.Log

/-!
# Soundness of the fixed-point logarithms of `AuxCore.Log`

`logQ_sound`: for positive naturals `a, b` and a valid enclosure of `log 2`, `logQ` encloses `2^p log (a / b)`.
-/

namespace AuxCommon

open AuxCore Real

/-- The `k`-th term `z^(2k+1)/(2k+1)` of the series of `atanh z`. -/
noncomputable def aterm (z : ℝ) (k : ℕ) : ℝ := z ^ (2 * k + 1) / (2 * (k : ℝ) + 1)

theorem aterm_nonneg {z : ℝ} (hz : 0 ≤ z) (k : ℕ) : 0 ≤ aterm z k := by
  unfold aterm; positivity

/-- `log ((1 + z) / (1 - z)) / 2 = ∑ z^(2k+1)/(2k+1)` for `0 ≤ z < 1`. -/
theorem hasSum_aterm {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    HasSum (aterm z) (log ((1 + z) / (1 - z)) / 2) := by
  have h := hasSum_log_sub_log_of_abs_lt_one (x := z) (by rw [abs_of_nonneg hz0]; exact hz1)
  rw [log_div (by linarith) (by linarith)]
  convert h.div_const 2 using 1
  funext k
  unfold aterm
  field_simp

theorem aterm_shift_le {z : ℝ} (hz0 : 0 ≤ z) (j k : ℕ) :
    aterm z (k + j) ≤ aterm z j * (z ^ 2) ^ k := by
  unfold aterm
  have hpow : z ^ (2 * (k + j) + 1) = z ^ (2 * j + 1) * (z ^ 2) ^ k := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [hpow, div_mul_eq_mul_div]
  have h1 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  have h2 : 2 * (j : ℝ) + 1 ≤ 2 * ((k + j : ℕ) : ℝ) + 1 := by
    push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  exact div_le_div_of_nonneg_left (by positivity) h1 h2

/-- The tail of the atanh series is at most `9/8` times its first term when `0 ≤ z ≤ 1/3`. -/
theorem tsum_aterm_tail_le {z : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ 1 / 3) (j : ℕ) :
    ∑' k : ℕ, aterm z (k + j) ≤ 9 / 8 * aterm z j := by
  have hz2 : z ^ 2 < 1 := by nlinarith
  have hz2' : 0 ≤ z ^ 2 := by positivity
  have hgeo : HasSum (fun k : ℕ => aterm z j * (z ^ 2) ^ k) (aterm z j * (1 - z ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hz2' hz2).mul_left _
  have hsum : Summable (fun k : ℕ => aterm z (k + j)) :=
    Summable.of_nonneg_of_le (fun k => aterm_nonneg hz0 _) (aterm_shift_le hz0 j) hgeo.summable
  calc ∑' k : ℕ, aterm z (k + j) ≤ aterm z j * (1 - z ^ 2)⁻¹ :=
        hasSum_le (aterm_shift_le hz0 j) hsum.hasSum hgeo
    _ ≤ aterm z j * (9 / 8) := by
        apply mul_le_mul_of_nonneg_left _ (aterm_nonneg hz0 j)
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        nlinarith
    _ = 9 / 8 * aterm z j := by ring

/-- `⌊m / d⌋ ≤ m / d` as reals. -/
theorem natCast_div_le' (m d : ℕ) : ((m / d : ℕ) : ℝ) ≤ (m : ℝ) / d := Nat.cast_div_le

/-- `m / d ≤ ⌈m / d⌉ = (m + d - 1) / d` as reals, for `d > 0`. -/
theorem le_natCast_ceil_div (m d : ℕ) (hd : 0 < d) : (m : ℝ) / d ≤ (((m + (d - 1)) / d : ℕ) : ℝ) := by
  have key : m ≤ (m + (d - 1)) / d * d := by
    have h1 := Nat.div_add_mod (m + (d - 1)) d
    have h2 := Nat.mod_lt (m + (d - 1)) hd
    rw [Nat.mul_comm]
    omega
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast key

/-- Lower-bound recursion of the series. -/
theorem atanhLoAux_le {p z2 : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hz2 : (z2 : ℝ) ≤ 2 ^ p * z ^ 2) :
    ∀ (n j pw : ℕ), (pw : ℝ) ≤ 2 ^ p * z ^ (2 * j + 1) →
      (atanhLoAux p z2 n j pw : ℝ) ≤ 2 ^ p * ∑ i ∈ Finset.range n, aterm z (i + j) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  intro n
  induction n with
  | zero => intro j pw _; simp [atanhLoAux]
  | succ n ih =>
    intro j pw hpw
    have hnext : (((pw * z2) >>> p : ℕ) : ℝ) ≤ 2 ^ p * z ^ (2 * (j + 1) + 1) := by
      rw [Nat.shiftRight_eq_div_pow]
      refine (natCast_div_le' _ _).trans ?_
      rw [div_le_iff₀ (by positivity)]
      push_cast
      calc (pw : ℝ) * z2 ≤ (2 ^ p * z ^ (2 * j + 1)) * (2 ^ p * z ^ 2) :=
            mul_le_mul hpw hz2 (Nat.cast_nonneg _) (by positivity)
        _ = 2 ^ p * z ^ (2 * (j + 1) + 1) * 2 ^ p := by ring
    have hrec := ih (j + 1) _ hnext
    have hterm : ((pw / (2 * j + 1) : ℕ) : ℝ) ≤ 2 ^ p * aterm z j := by
      refine (natCast_div_le' _ _).trans ?_
      unfold aterm
      push_cast
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hpw (by positivity)
    have hsum : ∑ i ∈ Finset.range (n + 1), aterm z (i + j) =
        aterm z j + ∑ i ∈ Finset.range n, aterm z (i + (j + 1)) := by
      rw [Finset.sum_range_succ', add_comm]
      congr 1
      · simp
      · apply Finset.sum_congr rfl; intro i _; congr 1; omega
    simp only [atanhLoAux, Nat.cast_add]
    rw [hsum, mul_add]
    linarith

/-- Upper-bound recursion of the series (with the tail bound at the end). -/
theorem le_atanhHiAux {p z2 : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hz13 : z ≤ 1 / 3)
    (hz2 : 2 ^ p * z ^ 2 ≤ (z2 : ℝ)) :
    ∀ (n j pw : ℕ), 2 ^ p * z ^ (2 * j + 1) ≤ (pw : ℝ) →
      2 ^ p * ∑' i : ℕ, aterm z (i + j) ≤ (atanhHiAux p z2 n j pw : ℝ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hz1 : z < 1 := by linarith
  have hsummable : ∀ j : ℕ, Summable (fun i : ℕ => aterm z (i + j)) := fun j =>
    (summable_nat_add_iff j).mpr (hasSum_aterm hz0 hz1).summable
  intro n
  induction n with
  | zero =>
    intro j pw hpw
    simp only [atanhHiAux]
    have hceil := le_natCast_ceil_div (9 * pw) (8 * (2 * j + 1)) (by omega)
    have htail := tsum_aterm_tail_le hz0 hz13 j
    calc 2 ^ p * ∑' i : ℕ, aterm z (i + j) ≤ 2 ^ p * (9 / 8 * aterm z j) :=
          mul_le_mul_of_nonneg_left htail hp.le
      _ = 9 * (2 ^ p * z ^ (2 * j + 1)) / (8 * (2 * (j : ℝ) + 1)) := by unfold aterm; field_simp
      _ ≤ 9 * (pw : ℝ) / (8 * (2 * (j : ℝ) + 1)) := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
      _ = ((9 * pw : ℕ) : ℝ) / ((8 * (2 * j + 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ _ := hceil
  | succ n ih =>
    intro j pw hpw
    have hnext : 2 ^ p * z ^ (2 * (j + 1) + 1) ≤ (((pw * z2 + (2 ^ p - 1)) >>> p : ℕ) : ℝ) := by
      rw [Nat.shiftRight_eq_div_pow]
      have hceil := le_natCast_ceil_div (pw * z2) (2 ^ p) (Nat.two_pow_pos p)
      refine le_trans ?_ hceil
      rw [le_div_iff₀ (by positivity)]
      push_cast
      calc 2 ^ p * z ^ (2 * (j + 1) + 1) * 2 ^ p = (2 ^ p * z ^ (2 * j + 1)) * (2 ^ p * z ^ 2) := by ring
        _ ≤ (pw : ℝ) * z2 := mul_le_mul hpw hz2 (by positivity) (Nat.cast_nonneg _)
    have hrec := ih (j + 1) _ hnext
    have hterm : 2 ^ p * aterm z j ≤ (((pw + 2 * j) / (2 * j + 1) : ℕ) : ℝ) := by
      have hceil := le_natCast_ceil_div pw (2 * j + 1) (by omega)
      have h2j : 2 * j + 1 - 1 = 2 * j := by omega
      rw [h2j] at hceil
      refine le_trans ?_ hceil
      unfold aterm
      push_cast
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hpw (by positivity)
    have hsplit : ∑' i : ℕ, aterm z (i + j) = aterm z j + ∑' i : ℕ, aterm z (i + (j + 1)) := by
      rw [(hsummable j).tsum_eq_zero_add]
      congr 1
      · simp
      · congr 1; funext i; congr 1; omega
    simp only [atanhHiAux, Nat.cast_add]
    rw [hsplit, mul_add]
    linarith

/-- `(1 + z)/(1 - z) = A/B` for `z = (A - B)/(A + B)`. -/
theorem atanh_arg {A B : ℕ} (hB : 0 < B) :
    (1 + ((A : ℝ) - B) / (A + B)) / (1 - ((A : ℝ) - B) / (A + B)) = (A : ℝ) / B := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hAB : (0 : ℝ) < (A : ℝ) + B := by positivity
  rw [div_eq_div_iff (by field_simp; ring_nf; positivity) hB'.ne']
  field_simp
  ring

/-- Lower bound: `logRatLo p J A B / 2^p ≤ log (A / B)` for `0 < B ≤ A`. -/
theorem logRatLo_le {p J A B : ℕ} (hB : 0 < B) (hBA : B ≤ A) :
    (logRatLo p J A B : ℝ) / 2 ^ p ≤ Real.log ((A : ℝ) / B) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hAB : (0 : ℝ) < (A : ℝ) + B := by positivity
  have hBA' : (B : ℝ) ≤ A := by exact_mod_cast hBA
  have hz0 : 0 ≤ ((A : ℝ) - B) / (A + B) := div_nonneg (by linarith) hAB.le
  have hz1 : ((A : ℝ) - B) / (A + B) < 1 := by rw [div_lt_one hAB]; linarith
  generalize hz : ((A : ℝ) - B) / (A + B) = z at hz0 hz1
  have hzl : (((A - B) * 2 ^ p / (A + B) : ℕ) : ℝ) ≤ 2 ^ p * z := by
    refine (natCast_div_le' _ _).trans (le_of_eq ?_)
    rw [← hz, Nat.cast_mul, Nat.cast_sub hBA]; push_cast; ring
  generalize hzl' : (A - B) * 2 ^ p / (A + B) = zl at hzl
  have hz2 : ((((zl * zl) >>> p) : ℕ) : ℝ) ≤ 2 ^ p * z ^ 2 := by
    rw [Nat.shiftRight_eq_div_pow]
    refine (natCast_div_le' _ _).trans ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    calc (zl : ℝ) * zl ≤ (2 ^ p * z) * (2 ^ p * z) := mul_le_mul hzl hzl (Nat.cast_nonneg _) (by positivity)
      _ = 2 ^ p * z ^ 2 * 2 ^ p := by ring
  have hmain := atanhLoAux_le hz0 hz2 J 0 zl (by simpa using hzl)
  have hsum : ∑ i ∈ Finset.range J, aterm z (i + 0) ≤ Real.log ((A : ℝ) / B) / 2 := by
    have := sum_le_hasSum (Finset.range J) (fun i _ => aterm_nonneg hz0 i) (hasSum_aterm hz0 hz1)
    have harg : (1 + z) / (1 - z) = (A : ℝ) / B := by rw [← hz]; exact atanh_arg hB
    rw [harg] at this
    simpa using this
  have hval : logRatLo p J A B = 2 * atanhLoAux p ((zl * zl) >>> p) J 0 zl := by
    simp only [logRatLo, hzl']
  rw [hval, div_le_iff₀ hp]
  push_cast
  nlinarith

/-- Upper bound: `log (A / B) ≤ logRatHi p J A B / 2^p` for `0 < B ≤ A ≤ 2B`. -/
theorem le_logRatHi {p J A B : ℕ} (hB : 0 < B) (hBA : B ≤ A) (hA2 : A ≤ 2 * B) :
    Real.log ((A : ℝ) / B) ≤ (logRatHi p J A B : ℝ) / 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hAB : (0 : ℝ) < (A : ℝ) + B := by positivity
  have hBA' : (B : ℝ) ≤ A := by exact_mod_cast hBA
  have hA2' : (A : ℝ) ≤ 2 * B := by exact_mod_cast hA2
  have hz0 : 0 ≤ ((A : ℝ) - B) / (A + B) := div_nonneg (by linarith) hAB.le
  have hz13 : ((A : ℝ) - B) / (A + B) ≤ 1 / 3 := by rw [div_le_iff₀ hAB]; linarith
  have hz1 : ((A : ℝ) - B) / (A + B) < 1 := by linarith
  generalize hz : ((A : ℝ) - B) / (A + B) = z at hz0 hz13 hz1
  have hzh : 2 ^ p * z ≤ ((((A - B) * 2 ^ p + (A + B - 1)) / (A + B) : ℕ) : ℝ) := by
    have hceil := le_natCast_ceil_div ((A - B) * 2 ^ p) (A + B) (by omega)
    refine le_trans (le_of_eq ?_) hceil
    rw [← hz, Nat.cast_mul, Nat.cast_sub hBA]; push_cast; ring
  generalize hzh' : ((A - B) * 2 ^ p + (A + B - 1)) / (A + B) = zh at hzh
  have hz2 : 2 ^ p * z ^ 2 ≤ (((zh * zh + (2 ^ p - 1)) >>> p : ℕ) : ℝ) := by
    rw [Nat.shiftRight_eq_div_pow]
    have hceil := le_natCast_ceil_div (zh * zh) (2 ^ p) (Nat.two_pow_pos p)
    refine le_trans ?_ hceil
    rw [le_div_iff₀ (by positivity)]
    push_cast
    calc 2 ^ p * z ^ 2 * 2 ^ p = (2 ^ p * z) * (2 ^ p * z) := by ring
      _ ≤ (zh : ℝ) * zh := mul_le_mul hzh hzh (by positivity) (Nat.cast_nonneg _)
  have hmain := le_atanhHiAux hz0 hz13 hz2 J 0 zh (by simpa using hzh)
  have htsum : ∑' i : ℕ, aterm z (i + 0) = Real.log ((A : ℝ) / B) / 2 := by
    simp only [add_zero]
    rw [(hasSum_aterm hz0 hz1).tsum_eq, ← hz, atanh_arg hB]
  rw [htsum] at hmain
  have hval : logRatHi p J A B = 2 * atanhHiAux p ((zh * zh + (2 ^ p - 1)) >>> p) J 0 zh := by
    simp only [logRatHi, hzh']
  rw [hval, le_div_iff₀ hp]
  push_cast
  nlinarith

/-- The reduction `logRed`: `B > 0`, `B ≤ A ≤ 2B`, and `a / b = 2^e · A / B`. -/
theorem logRed_spec {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    0 < (logRed a b).2.1 ∧ (logRed a b).2.1 ≤ (logRed a b).1 ∧ (logRed a b).1 ≤ 2 * (logRed a b).2.1 ∧
      (a : ℝ) / b = (2 : ℝ) ^ (logRed a b).2.2 * (((logRed a b).1 : ℝ) / (logRed a b).2.1) := by
  have hs1 : 2 ^ Nat.log2 a ≤ a := Nat.log2_self_le (by omega)
  have hs2 : a < 2 ^ (Nat.log2 a + 1) := Nat.lt_log2_self
  have ht1 : 2 ^ Nat.log2 b ≤ b := Nat.log2_self_le (by omega)
  have ht2 : b < 2 ^ (Nat.log2 b + 1) := Nat.lt_log2_self
  unfold logRed
  simp only [Nat.shiftLeft_eq, pow_one]
  generalize Nat.log2 a = s at *
  generalize Nat.log2 b = t at *
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have h2s : 0 < 2 ^ s := Nat.two_pow_pos s
  have h2t : 0 < 2 ^ t := Nat.two_pow_pos t
  -- X = a 2^t, Y = b 2^s, both in [2^(s+t), 2^(s+t+1))
  have hX1 : 2 ^ s * 2 ^ t ≤ a * 2 ^ t := Nat.mul_le_mul_right _ hs1
  have hX2 : a * 2 ^ t < 2 * (2 ^ s * 2 ^ t) := by
    have := Nat.mul_lt_mul_of_pos_right hs2 h2t; rw [pow_succ] at this; linarith
  have hY1 : 2 ^ s * 2 ^ t ≤ b * 2 ^ s := by
    have := Nat.mul_le_mul_right (2 ^ s) ht1; linarith [Nat.mul_comm (2 ^ t) (2 ^ s)]
  have hY2 : b * 2 ^ s < 2 * (2 ^ s * 2 ^ t) := by
    have := Nat.mul_lt_mul_of_pos_right ht2 h2s; rw [pow_succ] at this; linarith [Nat.mul_comm (2 ^ t) (2 ^ s)]
  have hYpos : 0 < b * 2 ^ s := Nat.mul_pos hb h2s
  split_ifs with h
  · dsimp only
    refine ⟨hYpos, h, by omega, ?_⟩
    rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
    push_cast
    field_simp
  · dsimp only
    refine ⟨hYpos, by omega, by omega, ?_⟩
    rw [zpow_sub₀ (by norm_num), zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, zpow_one]
    push_cast
    field_simp

/-- **Soundness of `logQ`.** -/
theorem logQ_sound {p J : ℕ} {l2lo l2hi : ℤ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hl2lo : (l2lo : ℝ) / 2 ^ p ≤ Real.log 2) (hl2hi : Real.log 2 ≤ (l2hi : ℝ) / 2 ^ p) :
    ((logQ p J l2lo l2hi a b).1 : ℝ) / 2 ^ p ≤ Real.log ((a : ℝ) / b) ∧
      Real.log ((a : ℝ) / b) ≤ ((logQ p J l2lo l2hi a b).2 : ℝ) / 2 ^ p := by
  obtain ⟨hB, hBA, hA2, heq⟩ := logRed_spec ha hb
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hlo := logRatLo_le (p := p) (J := J) hB hBA
  have hhi := le_logRatHi (p := p) (J := J) hB hBA hA2
  unfold logQ
  generalize logRed a b = r at hB hBA hA2 heq hlo hhi
  obtain ⟨A, B, e⟩ := r
  simp only at hB hBA hA2 heq hlo hhi ⊢
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hA' : (0 : ℝ) < A := by have : 0 < A := lt_of_lt_of_le hB hBA; exact_mod_cast this
  have hlog : Real.log ((a : ℝ) / b) = e * Real.log 2 + Real.log ((A : ℝ) / B) := by
    rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_zpow]
  rw [hlog]
  rw [div_le_iff₀ hp] at hl2lo hlo
  rw [le_div_iff₀ hp] at hl2hi hhi
  split_ifs with he
  · have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
    constructor
    · rw [div_le_iff₀ hp]; push_cast; nlinarith
    · rw [le_div_iff₀ hp]; push_cast; nlinarith
  · have he' : (e : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge he)
    constructor
    · rw [div_le_iff₀ hp]; push_cast; nlinarith
    · rw [le_div_iff₀ hp]; push_cast; nlinarith

end AuxCommon
