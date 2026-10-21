import TPMahler.AnaSound

/-!
# The tails of the check, and the per-polynomial terms of windows and tails

* `sum_slopeJump_Hk_le_log` (generic) and `UR_le_sR_log` (certificate): `U(x) ≤ s log x` for `x ≥ e_N`;
* `abs_QR_eval_le_tail`: `|Q(x)| ≤ x^d ∑ₙ |aₙ| x_t^{-n}` for `x ≥ x_t > 0` (`aₙ` the coefficient of `x^{d-n}`), and
  `rightTail_poly_term`: the term of `rightTailLB` for one polynomial;
* `encl_abs_le`, `encl_log_term`: `|Q| ≤ B / D^d` on `[Xp/D, (Xp + H)/D]` from `encl` (windows, left tail), and the
  corresponding term of `windowLB` / `leftTailLB`; `leftTail_x_term`: the term of `Q₀ = x` in `leftTailLB`;
* data facts of the certificate proved by kernel reduction (`decide +kernel`, no `native_decide`): `dataOK_true`,
  the lengths, `G₀ = G_N = 0`, increasing nodes, and `sR_eq_trapezoid`.
-/

open Polynomial Set MeasureTheory

namespace TPMahler.Cert

open TPCore

/-! ## `U(x) ≤ s log x` to the right of the support -/

/-- **Right tail of the potential (generic).** For nodes `0 ≤ e 0 < ⋯ < e N`, `G ≥ 0`, `G 0 = G N = 0` and
`x ≥ e N`: `∑ᵢ Cᵢ H(eᵢ - x) ≤ s log x`, `s = ∑ₖ (e_{k+1} - e_k)(G_k + G_{k+1})/2` (no `x ≥ 1` needed). -/
theorem sum_slopeJump_Hk_le_log {N : ℕ} {e G : ℕ → ℝ} (he : ∀ k < N, e k < e (k + 1))
    (hG : ∀ k ≤ N, 0 ≤ G k) (hG0 : G 0 = 0) (hGN : G N = 0) (he0 : 0 ≤ e 0) {x : ℝ} (hxN : e N ≤ x) :
    ∑ i ∈ Finset.range (N + 1), slopeJump N e G i * Hk (e i - x) ≤
      (∑ k ∈ Finset.range N, (e (k + 1) - e k) * (G k + G (k + 1)) / 2) * Real.log x := by
  rw [← integral_log_mul_pwLin he hG0 hGN x, ← integral_pwLin he, ← integral_mul_const]
  have hint1 : Integrable (fun y => Real.log |x - y| * pwLin N e G y) := by
    have h : (fun y => Real.log |x - y| * pwLin N e G y) = fun y => Real.log (y - x) * pwLin N e G y := by
      funext y
      rw [Real.log_abs, ← Real.log_neg_eq_log, neg_sub]
    rw [h]
    exact integrable_mul_pwLin x (intervalIntegrable_log_sub x) he
  have hint2 : Integrable (fun y => pwLin N e G y * Real.log x) := (integrable_pwLin N e G).mul_const _
  refine integral_mono hint1 hint2 (fun y => ?_)
  by_cases hy : y < e 0 ∨ e N ≤ y
  · rw [pwLin_eq_zero_of_notMem he hy]
    simp
  · push Not at hy
    obtain ⟨hy0, hyN⟩ := hy
    have hxy : 0 < x - y := by linarith
    have hlog : Real.log |x - y| ≤ Real.log x := by
      rw [abs_of_pos hxy]
      exact Real.log_le_log hxy (by linarith)
    have hg := pwLin_nonneg (e := e) hG y
    calc Real.log |x - y| * pwLin N e G y ≤ Real.log x * pwLin N e G y := mul_le_mul_of_nonneg_right hlog hg
      _ = pwLin N e G y * Real.log x := mul_comm _ _

/-! ## Data facts (kernel reduction) -/

set_option maxRecDepth 200000 in
/-- The data check of the certificate, by kernel reduction. -/
theorem dataOK_true : dataOK = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem nodes_length : nodes.length = NN + 1 := by decide +kernel

set_option maxRecDepth 200000 in
theorem gvals_length : gvals.length = NN + 1 := by decide +kernel

set_option maxRecDepth 200000 in
theorem gvals_first : gvals.getD 0 0 = 0 := by decide +kernel

set_option maxRecDepth 200000 in
theorem gvals_last : gvals.getD NN 0 = 0 := by decide +kernel

set_option maxRecDepth 200000 in
theorem nodes_first : nodes.getD 0 0 = 0 := by decide +kernel

set_option maxRecDepth 200000 in
theorem nodes_zip_inc : (List.zip nodes (nodes.drop 1)).all (fun x => decide (x.1 < x.2)) = true := by
  decide +kernel

theorem getD_lt_of_zip_all : ∀ (l : List ℕ), (List.zip l (l.drop 1)).all (fun x => decide (x.1 < x.2)) = true →
    ∀ k, k + 1 < l.length → l.getD k 0 < l.getD (k + 1) 0
  | [], _, k, hk => by simp at hk
  | [_], _, k, hk => by simp at hk
  | a :: b :: t, h, k, hk => by
    have h' : List.zip (a :: b :: t) ((a :: b :: t).drop 1) = (a, b) :: List.zip (b :: t) ((b :: t).drop 1) := by
      simp
    rw [h', List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := getD_lt_of_zip_all (b :: t) h.2 k (by simp at hk ⊢; omega)
      simpa using this

theorem nodes_inc : ∀ k < NN, nodes.getD k 0 < nodes.getD (k + 1) 0 :=
  fun k hk => getD_lt_of_zip_all nodes nodes_zip_inc k (by rw [nodes_length]; omega)

theorem eR_lt : ∀ k < NN, eR k < eR (k + 1) := by
  intro k hk
  unfold eR
  have h : (nodes.getD k 0 : ℝ) < nodes.getD (k + 1) 0 := by exact_mod_cast nodes_inc k hk
  have h10 : (0 : ℝ) < 10 ^ 10 := by positivity
  exact div_lt_div_of_pos_right h h10

theorem eR_zero : eR 0 = 0 := by
  unfold eR
  rw [nodes_first]
  simp

theorem GR_nonneg (k : ℕ) : 0 ≤ GR k := by
  unfold GR
  positivity

theorem GR_zero : GR 0 = 0 := by
  unfold GR
  rw [gvals_first]
  simp

theorem GR_NN : GR NN = 0 := by
  unfold GR
  rw [gvals_last]
  simp

/-- `sNumAux` is the trapezoid sum (integer form). -/
theorem sNumAux_eq_sum (m : ℕ) : ∀ (ns gs : List ℕ), ns.length = m + 1 → gs.length = m + 1 →
    (∀ k < m, ns.getD k 0 ≤ ns.getD (k + 1) 0) →
    (sNumAux ns gs : ℝ) = ∑ k ∈ Finset.range m,
      (((ns.getD (k + 1) 0 : ℕ) : ℝ) - (ns.getD k 0 : ℕ)) * (((gs.getD k 0 : ℕ) : ℝ) + (gs.getD (k + 1) 0 : ℕ)) := by
  induction m with
  | zero =>
    intro ns gs hn hg _
    rcases ns with _ | ⟨n0, _ | ⟨n1, ns⟩⟩
    · simp at hn
    · rcases gs with _ | ⟨g0, _ | ⟨g1, gs⟩⟩
      · simp at hg
      · simp [sNumAux]
      · simp at hg
    · simp at hn
  | succ m ih =>
    intro ns gs hn hg hinc
    rcases ns with _ | ⟨n0, _ | ⟨n1, ns⟩⟩
    · simp at hn
    · simp at hn
    rcases gs with _ | ⟨g0, _ | ⟨g1, gs⟩⟩
    · simp at hg
    · simp at hg
    have h01 : n0 ≤ n1 := by simpa using hinc 0 (by omega)
    have ih' := ih (n1 :: ns) (g1 :: gs) (by simpa using hn) (by simpa using hg)
      (fun k hk => by simpa using hinc (k + 1) (by omega))
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, zero_add] at ih' ⊢
    rw [← ih']
    have hs : sNumAux (n0 :: n1 :: ns) (g0 :: g1 :: gs) = (n1 - n0) * (g0 + g1) + sNumAux (n1 :: ns) (g1 :: gs) :=
      rfl
    rw [hs]
    push_cast [Nat.cast_sub h01]
    ring

/-- `s = ∑ₖ (e_{k+1} - e_k)(G_k + G_{k+1})/2` for the certificate. -/
theorem sR_eq_trapezoid : sR = ∑ k ∈ Finset.range NN, (eR (k + 1) - eR k) * (GR k + GR (k + 1)) / 2 := by
  unfold sR sNum sDen
  rw [sNumAux_eq_sum NN nodes gvals nodes_length gvals_length (fun k hk => (nodes_inc k hk).le)]
  unfold eR GR
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [DEC]
  push_cast
  field_simp
  ring

theorem sR_pos : 0 < sR := by
  have h := dataOK_true
  simp only [dataOK, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold sR
  have h1 : (0 : ℝ) < sNum := by exact_mod_cast h.2
  have h2 : (0 : ℝ) < sDen := by
    have : 0 < sDen := Nat.mul_pos (Nat.mul_pos (by norm_num) (by unfold DEC; norm_num)) (pow_pos (by norm_num) _)
    exact_mod_cast this
  exact div_pos h1 h2

/-- **Right tail of the potential (certificate).** `U(x) ≤ s log x` for `x ≥ e_N` (`= 11.2`). -/
theorem UR_le_sR_log {x : ℝ} (hxN : eR NN ≤ x) : UR x ≤ sR * Real.log x := by
  rw [sR_eq_trapezoid]
  exact sum_slopeJump_Hk_le_log eR_lt (fun k _ => GR_nonneg k) GR_zero GR_NN eR_zero.ge hxN

/-! ## Polynomials on the right tail -/

theorem foldl_horner_eq (x : ℝ) : ∀ (l : List ℤ) (c : ℝ),
    l.foldl (fun (acc : ℝ) (a : ℤ) => acc * x + (a : ℝ)) c =
      c * x ^ l.length + ∑ n ∈ Finset.range l.length, (l.getD n 0 : ℝ) * x ^ (l.length - 1 - n)
  | [], c => by simp
  | a :: t, c => by
    rw [List.foldl_cons, foldl_horner_eq x t, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have hsum : ∑ n ∈ Finset.range t.length, (t.getD n 0 : ℝ) * x ^ (t.length - 1 - n) =
        ∑ n ∈ Finset.range t.length, (t.getD n 0 : ℝ) * x ^ (t.length + 1 - 1 - (n + 1)) := by
      refine Finset.sum_congr rfl (fun n _ => ?_)
      congr 2
      omega
    rw [hsum, show t.length + 1 - 1 - 0 = t.length by omega, pow_succ]
    ring

/-- `Q(x) = ∑ₙ aₙ x^{d-n}` for the descending coefficients `aₙ`. -/
theorem QR_eval_eq_sum (l : List ℤ) (x : ℝ) :
    (QR l).eval x = ∑ n ∈ Finset.range l.length, (l.getD n 0 : ℝ) * x ^ (l.length - 1 - n) := by
  rw [QR_eval_eq, foldl_horner_eq]
  simp

/-- **Polynomial bound on the right tail**: `|Q(x)| ≤ x^d ∑ₙ |aₙ| x_t^{-n}` for `0 < x_t ≤ x`. -/
theorem abs_QR_eval_le_tail (l : List ℤ) {x xt : ℝ} (hxt : 0 < xt) (hx : xt ≤ x) :
    |(QR l).eval x| ≤ x ^ (l.length - 1) * ∑ n ∈ Finset.range l.length, |(l.getD n 0 : ℝ)| * xt⁻¹ ^ n := by
  have hx0 : 0 < x := lt_of_lt_of_le hxt hx
  rw [QR_eval_eq_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn' : n ≤ l.length - 1 := by
    have := Finset.mem_range.mp hn
    omega
  rw [abs_mul, abs_of_nonneg (pow_nonneg hx0.le _)]
  have h1 : x ^ (l.length - 1 - n) = x ^ (l.length - 1) * x⁻¹ ^ n := by
    rw [pow_sub₀ x hx0.ne' hn', inv_pow]
  have h2 : x⁻¹ ^ n ≤ xt⁻¹ ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hx0.le) (inv_anti₀ hxt hx) n
  rw [h1]
  have h3 : 0 ≤ x ^ (l.length - 1) := pow_nonneg hx0.le _
  calc |(l.getD n 0 : ℝ)| * (x ^ (l.length - 1) * x⁻¹ ^ n) ≤
        |(l.getD n 0 : ℝ)| * (x ^ (l.length - 1) * xt⁻¹ ^ n) := by gcongr
    _ = x ^ (l.length - 1) * (|(l.getD n 0 : ℝ)| * xt⁻¹ ^ n) := by ring

theorem foldl_zipIdx_add (f : Int × Nat → Nat) : ∀ (l : List Int) (k acc : Nat),
    (l.zipIdx k).foldl (fun a q => a + f q) acc = acc + ∑ i ∈ Finset.range l.length, f (l.getD i 0, k + i)
  | [], k, acc => by simp
  | c :: t, k, acc => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_zipIdx_add f t (k + 1) (acc + f (c, k)), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, add_zero]
    have hsum : ∑ i ∈ Finset.range t.length, f (t.getD i 0, k + 1 + i) =
        ∑ i ∈ Finset.range t.length, f (t.getD i 0, k + (i + 1)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      congr 2
      omega
    rw [hsum]
    ring

/-- The numerator of `rightTailLB` for one polynomial: `∑ₙ |aₙ| DEC^n Xt^(d-n)`. -/
theorem tailNum_eq (Xt : ℕ) (l : List ℤ) :
    ((l.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) 0 : ℕ) : ℝ) =
      ∑ n ∈ Finset.range l.length, |(l.getD n 0 : ℝ)| * (DEC : ℝ) ^ n * (Xt : ℝ) ^ (l.length - 1 - n) := by
  have h := foldl_zipIdx_add (fun q => q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) l 0 0
  simp only [zero_add] at h
  rw [h]
  push_cast
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem tailNum_div (l : List ℤ) {Xt : ℕ} (hXt : 0 < Xt) :
    ((l.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) 0 : ℕ) : ℝ) /
      (Xt : ℝ) ^ (l.length - 1) = ∑ n ∈ Finset.range l.length, |(l.getD n 0 : ℝ)| * ((Xt : ℝ) / DEC)⁻¹ ^ n := by
  have hX : (0 : ℝ) < Xt := by exact_mod_cast hXt
  have hD : (0 : ℝ) < (DEC : ℝ) := by
    unfold DEC
    norm_num
  rw [tailNum_eq, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hn' : n ≤ l.length - 1 := by
    have := Finset.mem_range.mp hn
    omega
  rw [pow_sub₀ (Xt : ℝ) hX.ne' hn', inv_div, div_pow]
  field_simp

/-- `|Q(x)| ≤ x^d · num / Xt^d` for `x ≥ Xt / DEC`, with `num` the numerator of `rightTailLB`. -/
theorem abs_QR_eval_le_tailNum (l : List ℤ) {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x) :
    |(QR l).eval x| ≤ x ^ (l.length - 1) *
      (((l.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) 0 : ℕ) :
        ℝ) / (Xt : ℝ) ^ (l.length - 1)) := by
  have hxt : (0 : ℝ) < (Xt : ℝ) / DEC := by
    have hX : (0 : ℝ) < Xt := by exact_mod_cast hXt
    have hD : (0 : ℝ) < (DEC : ℝ) := by
      unfold DEC
      norm_num
    positivity
  rw [tailNum_div l hXt]
  exact abs_QR_eval_le_tail l hxt hx

section logs

variable {tab : Nat} {l2 : Nat × Nat} {LD : Int × Int}

/-- **The term of `rightTailLB` for one polynomial**: with `num` its numerator and `d = deg Q`,
`fdiv (-cn (logT num Xt^d).2) 2^cs ≤ 2^P (-c (log |Q(x)| - d log x))` for `x ≥ Xt / DEC`, `Q(x) ≠ 0`. -/
theorem rightTail_poly_term
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    (l : List ℤ) {Xt : ℕ} (hXt : 0 < Xt) {x : ℝ} (hx : (Xt : ℝ) / DEC ≤ x) (hQ : (QR l).eval x ≠ 0)
    (cn cs : ℕ) :
    (fdiv (-(cn : Int) * (logT tab l2
        (l.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) 0)
        (Xt ^ (l.length - 1))).2) (2 ^ cs) : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(QR l).eval x| - (l.length - 1 : ℕ) * Real.log x)) := by
  set num := l.zipIdx.foldl (fun a (q : Int × Nat) => a + q.1.natAbs * DEC ^ q.2 * Xt ^ (l.length - 1 - q.2)) 0
    with hnum
  set d := l.length - 1 with hd
  have hX : (0 : ℝ) < Xt := by exact_mod_cast hXt
  have hDEC : (0 : ℝ) < (DEC : ℝ) := by
    unfold DEC
    norm_num
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hbound := abs_QR_eval_le_tailNum l hXt hx
  rw [← hnum, ← hd] at hbound
  have hQpos : 0 < |(QR l).eval x| := abs_pos.mpr hQ
  have hXd : (0 : ℝ) < (Xt : ℝ) ^ d := pow_pos hX d
  have hA : 0 < (num : ℝ) / (Xt : ℝ) ^ d := by
    by_contra hA
    push Not at hA
    have : x ^ d * ((num : ℝ) / (Xt : ℝ) ^ d) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hx0.le d) hA
    linarith
  have hnum0 : 0 < num := by
    have : (0 : ℝ) < num := by
      have := mul_pos hA hXd
      rwa [div_mul_cancel₀ _ hXd.ne'] at this
    exact_mod_cast this
  -- `log |Q x| - d log x ≤ log (num / Xt^d)`
  have hlogQ : Real.log |(QR l).eval x| - d * Real.log x ≤ Real.log ((num : ℝ) / (Xt : ℝ) ^ d) := by
    have h1 := Real.log_le_log hQpos hbound
    rw [Real.log_mul (pow_pos hx0 d).ne' hA.ne', Real.log_pow] at h1
    linarith
  have h2 := (hlog num (Xt ^ d) hnum0 (pow_pos hXt d)).2
  push_cast at h2
  have h3 := fdiv_le (-(cn : Int) * (logT tab l2 num (Xt ^ d)).2) (b := 2 ^ cs) (by positivity)
  push_cast at h3
  have hc : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
  have hcs : (0 : ℝ) < 2 ^ cs := by positivity
  refine h3.trans ?_
  rw [div_le_iff₀ hcs]
  have e : 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(QR l).eval x| - d * Real.log x)) * 2 ^ cs =
      -((cn : ℝ) * (2 ^ P * (Real.log |(QR l).eval x| - d * Real.log x))) := by
    field_simp
  rw [e]
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have := mul_le_mul_of_nonneg_left hlogQ hP.le
  have := mul_le_mul_of_nonneg_left (this.trans h2) hc
  linarith

/-- **The term of `Q₀ = x` in `leftTailLB`**: `fdiv (-cn (logT X0 D).2) 2^cs ≤ 2^P (-c log |x|)` for
`0 < x ≤ X0 / D`. -/
theorem leftTail_x_term
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    {X0 D : ℕ} (hX0 : 0 < X0) (hD : 0 < D) {x : ℝ} (hx0 : 0 < x) (hx : x ≤ (X0 : ℝ) / D) (cn cs : ℕ) :
    (fdiv (-(cn : Int) * (logT tab l2 X0 D).2) (2 ^ cs) : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR [1, 0]).eval x|) := by
  have hQ : (QR [1, 0]).eval x = x := by
    rw [QR_eval_eq]
    simp
  rw [hQ, abs_of_pos hx0]
  have h2 := (hlog X0 D hX0 hD).2
  have h3 := fdiv_le (-(cn : Int) * (logT tab l2 X0 D).2) (b := 2 ^ cs) (by positivity)
  push_cast at h3
  have hlx : Real.log x ≤ Real.log ((X0 : ℝ) / D) := Real.log_le_log hx0 hx
  have hc : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
  have hcs : (0 : ℝ) < 2 ^ cs := by positivity
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  refine h3.trans ?_
  rw [div_le_iff₀ hcs]
  have e : 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log x) * 2 ^ cs = -((cn : ℝ) * (2 ^ P * Real.log x)) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left hlx hP.le
  have := mul_le_mul_of_nonneg_left (this.trans h2) hc
  linarith

/-- `-c log x ≥ -c log x₀` for `0 < x ≤ x₀`, `c ≥ 0`. -/
theorem neg_mul_log_le_of_le {c x x0 : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hxx0 : x ≤ x0) :
    -c * Real.log x0 ≤ -c * Real.log x :=
  mul_le_mul_of_nonpos_left (Real.log_le_log hx hxx0) (neg_nonpos.mpr hc)

/-! ## Polynomials on windows and on the left tail (`encl` at `Xp`) -/

/-- `|Q(x)| ≤ B / D^d` on `[Xp / D, (Xp + H) / D]`, `B = max(|R₀.1|, |R₀.2|)`, `R₀ = encl H (taylorR Xp D desc)`. -/
theorem encl_abs_le {D : ℕ} (hD : 0 < D) (Xp H : ℕ) (desc : List ℤ) {x : ℝ}
    (hx0 : (Xp : ℝ) / D ≤ x) (hxH : x ≤ ((Xp : ℝ) + H) / D) :
    |(QR desc).eval x| ≤
      ((max (encl H (taylorR Xp D desc)).1.natAbs (encl H (taylorR Xp D desc)).2.natAbs : ℕ) : ℝ) /
        (D : ℝ) ^ (desc.length - 1) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hv0 : 0 ≤ (D : ℝ) * x - Xp := by
    rw [div_le_iff₀ hD'] at hx0
    linarith
  have hvH : (D : ℝ) * x - Xp ≤ H := by
    rw [le_div_iff₀ hD'] at hxH
    linarith
  obtain ⟨hlo, hhi⟩ := encl_spec hv0 hvH (taylorR Xp D desc)
  have hR := abs_le_max_abs_abs hlo hhi
  rw [(eval_eq_taylor hD Xp desc x).1, abs_div, abs_of_pos (pow_pos hD' _)]
  apply div_le_div_of_nonneg_right _ (pow_pos hD' _).le
  rw [Nat.cast_max, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  exact hR

/-- **The term of one polynomial in `windowLB` and in `leftTailLB`**: with `B` as in `encl_abs_le` and
`d = desc.length - 1`, `fdiv (-cn ((logT B 1).2 - d LD.1)) 2^cs ≤ 2^P (-c log |Q(x)|)` on
`[Xp / D, (Xp + H) / D]` where `Q(x) ≠ 0`. -/
theorem encl_log_term
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    {D : ℕ} (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2) (hD : 0 < D)
    (Xp H : ℕ) (desc : List ℤ) {x : ℝ} (hx0 : (Xp : ℝ) / D ≤ x) (hxH : x ≤ ((Xp : ℝ) + H) / D)
    (hQ : (QR desc).eval x ≠ 0) (cn cs : ℕ) :
    (fdiv (-(cn : Int) * ((logT tab l2
        (max (encl H (taylorR Xp D desc)).1.natAbs (encl H (taylorR Xp D desc)).2.natAbs) 1).2 -
        ((desc.length - 1 : ℕ) : Int) * LD.1)) (2 ^ cs) : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval x|) := by
  set B := max (encl H (taylorR Xp D desc)).1.natAbs (encl H (taylorR Xp D desc)).2.natAbs with hB
  set d := desc.length - 1 with hd
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hbound := encl_abs_le hD Xp H desc hx0 hxH
  rw [← hB, ← hd] at hbound
  have hQpos : 0 < |(QR desc).eval x| := abs_pos.mpr hQ
  have hBpos : (0 : ℝ) < B := by
    have h1 := lt_of_lt_of_le hQpos hbound
    have h2 : (0 : ℝ) < (D : ℝ) ^ d := pow_pos hD' d
    have := mul_pos h1 h2
    rwa [div_mul_cancel₀ _ h2.ne'] at this
  have hB0 : ((B : ℕ) : ℤ) ≠ 0 := by
    have : 0 < B := by exact_mod_cast hBpos
    exact_mod_cast this.ne'
  have hm := mcLogLo_le hlog hLD hB0 cn cs d
  have hlogQ : Real.log |(QR desc).eval x| ≤ Real.log |((B : ℕ) : ℤ)| - d * Real.log D := by
    have h1 := Real.log_le_log hQpos hbound
    rw [Real.log_div hBpos.ne' (pow_pos hD' d).ne', Real.log_pow] at h1
    have e : |(((B : ℕ) : ℤ) : ℝ)| = (B : ℝ) := by
      rw [Int.cast_natCast, abs_of_pos hBpos]
    rw [e]
    exact h1
  have hc : (0 : ℝ) ≤ (cn : ℝ) / 2 ^ cs := by positivity
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  refine (show (fdiv (-(cn : Int) * ((logT tab l2 B 1).2 - (d : Int) * LD.1)) (2 ^ cs) : ℝ) =
      (mcLogLo tab l2 cn cs d ((B : ℕ) : ℤ) LD : ℝ) from rfl).le.trans (hm.trans ?_)
  have := mul_le_mul_of_nonneg_left hlogQ hc
  have := mul_le_mul_of_nonneg_left this hP.le
  linarith

end logs

end TPMahler.Cert
