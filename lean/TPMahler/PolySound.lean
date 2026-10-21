import TPMahler.CertDefs

/-!
# Soundness of the polynomial routines of the checker

Real semantics of the integer polynomial routines of `TPCore.Check`:

* `evalAscR g v = ∑ gₙ vⁿ` for an ascending coefficient list `g`;
* `taylorR_spec`: `taylorR X D desc` has the ascending coefficients of `R(v) = D^d Q((X + v)/D)`, `Q = QR desc`,
  `d = desc.length - 1`;
* `derivAsc_spec`, `encl_spec`, `evalAsc_spec`: derivative, enclosure on `[0, H]`, exact evaluation;
* `polyLeaf_*`: the semantics of `polyLeaf` (no zero of `Q` on `[p, q]`; lower bounds of `-c log |Q|` at the ends;
  the `M` part; convexity and the tangent data).
-/

open Polynomial

namespace TPMahler.Cert

open TPCore

/-! ## Evaluation of ascending coefficient lists -/

/-- The real value `∑ gₙ vⁿ` of an ascending coefficient list `g` (Horner). -/
noncomputable def evalAscR (g : List Int) (v : ℝ) : ℝ := g.foldr (fun c acc => (c : ℝ) + v * acc) 0

@[simp] theorem evalAscR_nil (v : ℝ) : evalAscR [] v = 0 := rfl

@[simp] theorem evalAscR_cons (c : Int) (g : List Int) (v : ℝ) :
    evalAscR (c :: g) v = c + v * evalAscR g v := rfl

theorem evalAscR_zero (g : List Int) : evalAscR g 0 = (g.headD 0 : ℝ) := by
  cases g with
  | nil => simp
  | cons c t => simp

/-- `evalAsc` is exact. -/
theorem evalAsc_spec (H : Int) (g : List Int) : ((evalAsc H g : Int) : ℝ) = evalAscR g H := by
  induction g with
  | nil => simp [evalAsc]
  | cons c t ih =>
    have h : evalAsc H (c :: t) = c + H * evalAsc H t := rfl
    rw [h, evalAscR_cons, ← ih]
    push_cast
    ring

/-! ## `mulVX` and `taylorR` -/

theorem evalAscR_addHead (c : Int) (l : List Int) (v : ℝ) :
    evalAscR (mulVX.addHead c l) v = c + evalAscR l v := by
  cases l with
  | nil => simp [mulVX.addHead]
  | cons h t =>
    simp only [mulVX.addHead, evalAscR_cons]
    push_cast
    ring

theorem evalAscR_mulVX (X : Int) (r : List Int) (v : ℝ) :
    evalAscR (mulVX X r) v = (v + X) * evalAscR r v := by
  induction r with
  | nil => simp [mulVX]
  | cons r0 rs ih =>
    simp only [mulVX, evalAscR_cons, evalAscR_addHead, ih]
    push_cast
    ring

/-- One step of `taylorR`. -/
def tStep (X D : Nat) (st : List Int × Int) (a : Int) : List Int × Int :=
  match st with
  | (r, dp) => (match mulVX (X : Int) r with
                | [] => [a * dp]
                | h :: t => (h + a * dp) :: t, dp * (D : Int))

theorem taylorR_eq (X D : Nat) (desc : List Int) :
    taylorR X D desc = (desc.foldl (tStep X D) ([], 1)).1 := rfl

theorem tStep_snd (X D : Nat) (r : List Int) (dp a : Int) : (tStep X D (r, dp) a).2 = dp * (D : Int) := rfl

theorem tStep_fst (X D : Nat) (r : List Int) (dp a : Int) (v : ℝ) :
    evalAscR (tStep X D (r, dp) a).1 v = (v + X) * evalAscR r v + a * dp := by
  have hm := evalAscR_mulVX (X : Int) r v
  simp only [tStep]
  split
  · next h =>
    rw [h, evalAscR_nil] at hm
    simp only [evalAscR_cons, evalAscR_nil]
    push_cast
    push_cast at hm
    rw [← hm]
    ring
  · next h t ht =>
    rw [ht, evalAscR_cons] at hm
    simp only [evalAscR_cons]
    push_cast
    push_cast at hm
    rw [← hm]
    ring

theorem tStep_fold (X D : Nat) (hD : (D : ℝ) ≠ 0) (v : ℝ) :
    ∀ (l r : List Int) (dp : Int) (h : ℝ), (D : ℝ) * evalAscR r v = dp * h →
      (D : ℝ) * evalAscR (l.foldl (tStep X D) (r, dp)).1 v =
        ((l.foldl (tStep X D) (r, dp)).2 : ℝ) * l.foldl (fun acc (a : Int) => acc * ((X + v) / D) + (a : ℝ)) h ∧
      (l.foldl (tStep X D) (r, dp)).2 = dp * (D : Int) ^ l.length := by
  intro l
  induction l with
  | nil =>
    intro r dp h hr
    simpa using hr
  | cons a l ih =>
    intro r dp h hr
    simp only [List.foldl_cons]
    have hst : tStep X D (r, dp) a = ((tStep X D (r, dp) a).1, (tStep X D (r, dp) a).2) := rfl
    rw [hst]
    have key : (D : ℝ) * evalAscR (tStep X D (r, dp) a).1 v =
        ((tStep X D (r, dp) a).2 : ℝ) * (h * ((X + v) / D) + a) := by
      rw [tStep_fst, tStep_snd]
      push_cast
      have : (D : ℝ) * ((v + X) * evalAscR r v + a * dp) = (v + X) * (D * evalAscR r v) + a * dp * D := by ring
      rw [this, hr]
      field_simp
      ring
    obtain ⟨h1, h2⟩ := ih _ _ _ key
    refine ⟨h1, ?_⟩
    rw [h2, tStep_snd, List.length_cons, pow_succ]
    ring

/-- **`taylorR`**: the ascending coefficients of `R(v) = D^d Q((X + v)/D)`, `d = desc.length - 1`. -/
theorem taylorR_spec {D : Nat} (hD : 0 < D) (X : Nat) (desc : List Int) (v : ℝ) :
    evalAscR (taylorR X D desc) v = (D : ℝ) ^ (desc.length - 1) * (QR desc).eval ((X + v) / D) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨h1, h2⟩ := tStep_fold X D hD' v desc [] 1 0 (by simp)
  rw [taylorR_eq, QR_eval_eq]
  rw [h2] at h1
  push_cast at h1
  rcases Nat.eq_zero_or_pos desc.length with hl | hl
  · rw [List.length_eq_zero_iff] at hl
    subst hl
    simp
  · have hpow : (D : ℝ) ^ desc.length = D * D ^ (desc.length - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow, one_mul, mul_assoc] at h1
    exact mul_left_cancel₀ hD' h1

/-! ## `derivAsc` -/

/-- `derivAsc` with an index offset. -/
def dmap (k : Nat) (l : List Int) : List Int := (l.zipIdx k).map (fun (c, i) => c * ((i + 1 : Nat) : Int))

theorem derivAsc_eq (g : List Int) : derivAsc g = dmap 0 (g.drop 1) := rfl

@[simp] theorem dmap_nil (k : Nat) : dmap k [] = [] := rfl

theorem dmap_cons (k : Nat) (c : Int) (t : List Int) :
    dmap k (c :: t) = c * ((k + 1 : Nat) : Int) :: dmap (k + 1) t := rfl

theorem evalAscR_dmap (v : ℝ) : ∀ (l : List Int) (k : Nat),
    evalAscR (dmap k l) v = evalAscR (dmap 0 l) v + k * evalAscR l v := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons c t ih =>
    intro k
    rw [dmap_cons, dmap_cons, evalAscR_cons, evalAscR_cons, ih (k + 1), ih (0 + 1), evalAscR_cons]
    push_cast
    ring

theorem evalAscR_dmap_zero (v : ℝ) (t : List Int) :
    evalAscR (dmap 0 t) v = evalAscR t v + v * evalAscR (dmap 0 (t.drop 1)) v := by
  cases t with
  | nil => simp
  | cons c t =>
    rw [dmap_cons, evalAscR_cons, evalAscR_dmap v t (0 + 1), List.drop_one, List.tail_cons, evalAscR_cons]
    push_cast
    ring

/-- **`derivAsc`** is the derivative. -/
theorem derivAsc_spec (g : List Int) (v : ℝ) : HasDerivAt (evalAscR g) (evalAscR (derivAsc g) v) v := by
  induction g generalizing v with
  | nil =>
    have : evalAscR [] = fun _ => 0 := rfl
    rw [this, derivAsc_eq]
    simpa using hasDerivAt_const v (0 : ℝ)
  | cons c t ih =>
    have hf : evalAscR (c :: t) = fun w => (c : ℝ) + w * evalAscR t w := rfl
    rw [hf, derivAsc_eq, List.drop_one, List.tail_cons, evalAscR_dmap_zero, ← derivAsc_eq]
    have h := (hasDerivAt_const v (c : ℝ)).add ((hasDerivAt_id' v).mul (ih v))
    convert h using 1
    ring

/-! ## `encl` -/

/-- One step of `encl`. -/
def eStep (H : Nat) (acc : Int × Int) (q : Int × Nat) : Int × Int :=
  let v : Int := q.1 * (H : Int) ^ (q.2 + 1)
  if v < 0 then (acc.1 + v, acc.2) else (acc.1, acc.2 + v)

theorem encl_nil (H : Nat) : encl H [] = (0, 0) := rfl

theorem encl_cons (H : Nat) (c0 : Int) (t : List Int) :
    encl H (c0 :: t) = (t.zipIdx.foldl (eStep H) (c0, c0)) := rfl

theorem eStep_spec {H : Nat} {v : ℝ} (hv0 : 0 ≤ v) (hvH : v ≤ H) (lo hi : Int) (c : Int) (k : Nat) (y : ℝ)
    (hlo : (lo : ℝ) ≤ y) (hhi : y ≤ hi) :
    ((eStep H (lo, hi) (c, k)).1 : ℝ) ≤ y + c * v ^ (k + 1) ∧ y + c * v ^ (k + 1) ≤ (eStep H (lo, hi) (c, k)).2 := by
  have hw0 : 0 ≤ v ^ (k + 1) := pow_nonneg hv0 _
  have hwP : v ^ (k + 1) ≤ (H : ℝ) ^ (k + 1) := pow_le_pow_left₀ hv0 hvH _
  simp only [eStep]
  split
  · next hneg =>
    have hneg' : (c : ℝ) * (H : ℝ) ^ (k + 1) < 0 := by exact_mod_cast hneg
    have hP0 : 0 ≤ (H : ℝ) ^ (k + 1) := by positivity
    have hc : (c : ℝ) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_nonneg hc.le hP0
      linarith
    push_cast
    constructor
    · nlinarith
    · nlinarith
  · next hpos =>
    have hpos' : 0 ≤ (c : ℝ) * (H : ℝ) ^ (k + 1) := by
      push Not at hpos
      exact_mod_cast hpos
    push_cast
    rcases le_or_gt 0 (c : ℝ) with hc | hc
    · constructor
      · nlinarith
      · nlinarith
    · -- `c < 0` forces `H = 0`, hence `v = 0`
      have hP : (H : ℝ) ^ (k + 1) = 0 := by
        have hP0 : 0 ≤ (H : ℝ) ^ (k + 1) := by positivity
        by_contra hne
        have hPpos : 0 < (H : ℝ) ^ (k + 1) := lt_of_le_of_ne hP0 (Ne.symm hne)
        have := mul_neg_of_neg_of_pos hc hPpos
        linarith
      have hw : v ^ (k + 1) = 0 := le_antisymm (hP ▸ hwP) hw0
      rw [hw, hP]
      constructor <;> linarith

theorem eStep_fold {H : Nat} {v : ℝ} (hv0 : 0 ≤ v) (hvH : v ≤ H) :
    ∀ (t : List Int) (k : Nat) (lo hi : Int) (y : ℝ), (lo : ℝ) ≤ y → y ≤ hi →
      (((t.zipIdx k).foldl (eStep H) (lo, hi)).1 : ℝ) ≤ y + v ^ (k + 1) * evalAscR t v ∧
      y + v ^ (k + 1) * evalAscR t v ≤ ((t.zipIdx k).foldl (eStep H) (lo, hi)).2 := by
  intro t
  induction t with
  | nil => intro k lo hi y hlo hhi; simpa using ⟨hlo, hhi⟩
  | cons c t ih =>
    intro k lo hi y hlo hhi
    rw [List.zipIdx_cons, List.foldl_cons]
    obtain ⟨h1, h2⟩ := eStep_spec hv0 hvH lo hi c k y hlo hhi
    have hst : eStep H (lo, hi) (c, k) = ((eStep H (lo, hi) (c, k)).1, (eStep H (lo, hi) (c, k)).2) := rfl
    rw [hst]
    obtain ⟨h3, h4⟩ := ih (k + 1) _ _ _ h1 h2
    have e : y + c * v ^ (k + 1) + v ^ (k + 1 + 1) * evalAscR t v = y + v ^ (k + 1) * evalAscR (c :: t) v := by
      rw [evalAscR_cons, pow_succ]
      ring
    rw [e] at h3 h4
    exact ⟨h3, h4⟩

/-- **`encl`** encloses the polynomial on `[0, H]`. -/
theorem encl_spec {H : Nat} {v : ℝ} (hv0 : 0 ≤ v) (hvH : v ≤ H) (g : List Int) :
    ((encl H g).1 : ℝ) ≤ evalAscR g v ∧ evalAscR g v ≤ (encl H g).2 := by
  cases g with
  | nil => simp [encl_nil]
  | cons c0 t =>
    rw [encl_cons, evalAscR_cons]
    have := eStep_fold hv0 hvH t 0 c0 c0 (c0 : ℝ) le_rfl le_rfl
    simpa using this


/-! ## Derivatives of `R` and the values of `Q`, `Q'`, `Q''` -/

theorem taylorR_deriv1 {D : Nat} (hD : 0 < D) (X : Nat) (desc : List Int) (v : ℝ) :
    evalAscR (derivAsc (taylorR X D desc)) v =
      (D : ℝ) ^ (desc.length - 1) / D * (derivative (QR desc)).eval ((X + v) / D) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 := derivAsc_spec (taylorR X D desc) v
  have hfun : evalAscR (taylorR X D desc) =
      fun w : ℝ => (D : ℝ) ^ (desc.length - 1) * (QR desc).eval (((X : ℝ) + w) / D) :=
    funext (taylorR_spec hD X desc)
  rw [hfun] at h1
  have hin : HasDerivAt (fun w : ℝ => ((X : ℝ) + w) / D) (1 / D) v :=
    ((hasDerivAt_id' v).const_add (X : ℝ)).div_const (D : ℝ)
  have h2 := (((QR desc).hasDerivAt (((X : ℝ) + v) / D)).comp v hin).const_mul
    ((D : ℝ) ^ (desc.length - 1))
  rw [h1.unique h2]
  field_simp

theorem taylorR_deriv2 {D : Nat} (hD : 0 < D) (X : Nat) (desc : List Int) (v : ℝ) :
    evalAscR (derivAsc (derivAsc (taylorR X D desc))) v =
      (D : ℝ) ^ (desc.length - 1) / D ^ 2 * (derivative (derivative (QR desc))).eval ((X + v) / D) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have h1 := derivAsc_spec (derivAsc (taylorR X D desc)) v
  have hfun : evalAscR (derivAsc (taylorR X D desc)) =
      fun w : ℝ => (D : ℝ) ^ (desc.length - 1) / D * (derivative (QR desc)).eval (((X : ℝ) + w) / D) :=
    funext (taylorR_deriv1 hD X desc)
  rw [hfun] at h1
  have hin : HasDerivAt (fun w : ℝ => ((X : ℝ) + w) / D) (1 / D) v :=
    ((hasDerivAt_id' v).const_add (X : ℝ)).div_const (D : ℝ)
  have h2 := (((derivative (QR desc)).hasDerivAt (((X : ℝ) + v) / D)).comp v hin).const_mul
    ((D : ℝ) ^ (desc.length - 1) / D)
  rw [h1.unique h2]
  field_simp

/-- `Q`, `Q'`, `Q''` at `x` from `R`, `R'`, `R''` at `v = D x - X`. -/
theorem eval_eq_taylor {D : Nat} (hD : 0 < D) (X : Nat) (desc : List Int) (x : ℝ) :
    (QR desc).eval x = evalAscR (taylorR X D desc) (D * x - X) / D ^ (desc.length - 1) ∧
    (derivative (QR desc)).eval x =
      evalAscR (derivAsc (taylorR X D desc)) (D * x - X) * D / D ^ (desc.length - 1) ∧
    (derivative (derivative (QR desc))).eval x =
      evalAscR (derivAsc (derivAsc (taylorR X D desc))) (D * x - X) * D ^ 2 / D ^ (desc.length - 1) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hx : ((X : ℝ) + (D * x - X)) / D = x := by field_simp; ring
  have hpow : (D : ℝ) ^ (desc.length - 1) ≠ 0 := pow_ne_zero _ hD'
  refine ⟨?_, ?_, ?_⟩
  · rw [taylorR_spec hD, hx]
    field_simp
  · rw [taylorR_deriv1 hD, hx]
    field_simp
  · rw [taylorR_deriv2 hD, hx]
    field_simp

/-! ## Derivatives of `log |P|` -/

theorem hasDerivAt_log_abs_eval (Q : ℝ[X]) {x : ℝ} (hx : Q.eval x ≠ 0) :
    HasDerivAt (fun y => Real.log |Q.eval y|) ((derivative Q).eval x / Q.eval x) x := by
  have hfun : (fun y => Real.log |Q.eval y|) = fun y => Real.log (Q.eval y) :=
    funext fun y => Real.log_abs _
  rw [hfun]
  exact (Q.hasDerivAt x).log hx

theorem hasDerivAt_logDeriv_eval (Q : ℝ[X]) {x : ℝ} (hx : Q.eval x ≠ 0) :
    HasDerivAt (fun y => (derivative Q).eval y / Q.eval y)
      (((derivative (derivative Q)).eval x * Q.eval x - ((derivative Q).eval x) ^ 2) / (Q.eval x) ^ 2) x := by
  refine (((derivative Q).hasDerivAt x).div (Q.hasDerivAt x) hx).congr_deriv ?_
  ring

/-- First derivative of `-c log |Q|`. -/
theorem hasDerivAt_neg_mul_log_abs_eval (Q : ℝ[X]) (c : ℝ) {x : ℝ} (hx : Q.eval x ≠ 0) :
    HasDerivAt (fun y => -c * Real.log |Q.eval y|) (-c * ((derivative Q).eval x / Q.eval x)) x :=
  (hasDerivAt_log_abs_eval Q hx).const_mul (-c)

/-- Second derivative of `-c log |Q|`: `c (Q'² - Q Q'') / Q²`. -/
theorem hasDerivAt_neg_mul_logDeriv_eval (Q : ℝ[X]) (c : ℝ) {x : ℝ} (hx : Q.eval x ≠ 0) :
    HasDerivAt (fun y => -c * ((derivative Q).eval y / Q.eval y))
      (c * ((derivative Q).eval x ^ 2 - Q.eval x * (derivative (derivative Q)).eval x) / (Q.eval x) ^ 2) x := by
  convert (hasDerivAt_logDeriv_eval Q hx).const_mul (-c) using 1
  field_simp
  ring

/-! ## Integer rounding and interval products -/

theorem fdiv_le (a : Int) {b : Nat} (hb : 0 < b) : (fdiv a b : ℝ) ≤ a / b := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  rw [le_div_iff₀ hb']
  have h : fdiv a b = a / (b : ℤ) := rfl
  rw [h]
  have := Int.ediv_mul_le a (b := (b : ℤ)) (by exact_mod_cast hb.ne')
  exact_mod_cast this

theorem le_cdiv (a : Int) {b : Nat} (hb : 0 < b) : (a : ℝ) / b ≤ cdiv a b := by
  have h : cdiv a b = -(fdiv (-a) b) := rfl
  rw [h]
  have := fdiv_le (-a) hb
  push_cast at this ⊢
  rw [neg_div] at this
  linarith

theorem min4_le_mul {a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2) (hy1 : b1 ≤ y) (hy2 : y ≤ b2) :
    min (min (a1 * b1) (a1 * b2)) (min (a2 * b1) (a2 * b2)) ≤ x * y := by
  rcases le_or_gt 0 y with hy | hy
  · have h1 : a1 * y ≤ x * y := mul_le_mul_of_nonneg_right hx1 hy
    rcases le_or_gt 0 a1 with ha | ha
    · have : a1 * b1 ≤ a1 * y := mul_le_mul_of_nonneg_left hy1 ha
      exact (min_le_left _ _).trans ((min_le_left _ _).trans (this.trans h1))
    · have : a1 * b2 ≤ a1 * y := by nlinarith
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (this.trans h1))
  · have h1 : a2 * y ≤ x * y := by nlinarith
    rcases le_or_gt 0 a2 with ha | ha
    · have : a2 * b1 ≤ a2 * y := mul_le_mul_of_nonneg_left hy1 ha
      exact (min_le_right _ _).trans ((min_le_left _ _).trans (this.trans h1))
    · have : a2 * b2 ≤ a2 * y := by nlinarith
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (this.trans h1))

theorem mul_le_max4 {a1 a2 b1 b2 x y : ℝ} (hx1 : a1 ≤ x) (hx2 : x ≤ a2) (hy1 : b1 ≤ y) (hy2 : y ≤ b2) :
    x * y ≤ max (max (a1 * b1) (a1 * b2)) (max (a2 * b1) (a2 * b2)) := by
  rcases le_or_gt 0 y with hy | hy
  · have h1 : x * y ≤ a2 * y := mul_le_mul_of_nonneg_right hx2 hy
    rcases le_or_gt 0 a2 with ha | ha
    · have : a2 * y ≤ a2 * b2 := mul_le_mul_of_nonneg_left hy2 ha
      exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_right _ _))
    · have : a2 * y ≤ a2 * b1 := by nlinarith
      exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h1 : x * y ≤ a1 * y := by nlinarith
    rcases le_or_gt 0 a1 with ha | ha
    · have : a1 * y ≤ a1 * b2 := mul_le_mul_of_nonneg_left hy2 ha
      exact (h1.trans this).trans ((le_max_right _ _).trans (le_max_left _ _))
    · have : a1 * y ≤ a1 * b1 := by nlinarith
      exact (h1.trans this).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- `imul` encloses products. -/
theorem imul_spec {a b : Int × Int} {x y : ℝ} (hx : (a.1 : ℝ) ≤ x ∧ x ≤ a.2) (hy : (b.1 : ℝ) ≤ y ∧ y ≤ b.2) :
    ((imul a b).1 : ℝ) ≤ x * y ∧ x * y ≤ (imul a b).2 := by
  simp only [imul]
  push_cast
  exact ⟨min4_le_mul hx.1 hx.2 hy.1 hy.2, mul_le_max4 hx.1 hx.2 hy.1 hy.2⟩

/-! ## `mcLogLo` -/

section logs

variable {tab : Nat} {l2 : Nat × Nat} {LD : Int × Int}

/-- `mcLogLo` is a lower bound of `2^P (-c (log |W| - d log D))`. -/
theorem mcLogLo_le
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    {D : Nat} (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2)
    {W : Int} (hW : W ≠ 0) (cn cs d : Nat) :
    (mcLogLo tab l2 cn cs d W LD : ℝ) ≤
      2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(W : ℝ)| - d * Real.log D)) := by
  unfold mcLogLo
  have h1 := fdiv_le (-(cn : ℤ) * ((logT tab l2 W.natAbs 1).2 - (d : ℤ) * LD.1)) (b := 2 ^ cs) (by positivity)
  have h2 := (hlog W.natAbs 1 (Int.natAbs_pos.mpr hW) one_pos).2
  rw [Nat.cast_natAbs, Nat.cast_one, div_one] at h2
  have h3 := hLD.1
  push_cast at h1 h2
  have hc : (0 : ℝ) ≤ cn := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hcs : (0 : ℝ) < 2 ^ cs := by positivity
  refine h1.trans ?_
  rw [div_le_iff₀ hcs]
  have key : (cn : ℝ) * (2 ^ P * Real.log |(W : ℝ)| - d * (2 ^ P * Real.log D)) ≤
      cn * ((logT tab l2 W.natAbs 1).2 - d * LD.1) := by
    apply mul_le_mul_of_nonneg_left _ hc
    have := mul_le_mul_of_nonneg_left h3 hd
    linarith
  have e : 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (Real.log |(W : ℝ)| - d * Real.log D)) * 2 ^ cs =
      -((cn : ℝ) * (2 ^ P * Real.log |(W : ℝ)| - d * (2 ^ P * Real.log D))) := by
    field_simp
  rw [e]
  linarith

end logs

/-! ## Constant sign of `R` on `[0, H]` -/

theorem natAbs_min_le_abs {lo hi : Int} {y : ℝ} (hlo : (lo : ℝ) ≤ y) (hhi : y ≤ hi) (h : 0 < lo ∨ hi < 0) :
    ((min lo.natAbs hi.natAbs : ℕ) : ℝ) ≤ |y| ∧ 0 < min lo.natAbs hi.natAbs := by
  rw [Nat.cast_min, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  rcases h with h | h
  · have hl : (0 : ℝ) < lo := by exact_mod_cast h
    have hh : (0 : ℝ) < hi := lt_of_lt_of_le hl (hlo.trans hhi)
    have hh' : 0 < hi := by exact_mod_cast hh
    refine ⟨?_, ?_⟩
    · rw [abs_of_pos hl, abs_of_pos (lt_of_lt_of_le hl hlo)]
      exact (min_le_left _ _).trans hlo
    · exact lt_min (Int.natAbs_pos.mpr h.ne') (Int.natAbs_pos.mpr hh'.ne')
  · have hh : (hi : ℝ) < 0 := by exact_mod_cast h
    have hl : (lo : ℝ) < 0 := lt_of_le_of_lt (hlo.trans hhi) hh
    have hl' : lo < 0 := by exact_mod_cast hl
    refine ⟨?_, ?_⟩
    · rw [abs_of_neg hh, abs_of_neg (lt_of_le_of_lt hhi hh)]
      exact (min_le_right _ _).trans (by linarith)
    · exact lt_min (Int.natAbs_pos.mpr hl'.ne) (Int.natAbs_pos.mpr h.ne)

theorem between_abs {a b y : ℝ} (hy : (a ≤ y ∧ y ≤ b) ∨ (b ≤ y ∧ y ≤ a)) (hab : 0 < a * b) :
    min |a| |b| ≤ |y| ∧ y ≠ 0 := by
  rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [abs_of_pos ha, abs_of_pos hb]
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos (lt_of_lt_of_le ha h1)]
      exact ⟨(min_le_left _ _).trans h1, (lt_of_lt_of_le ha h1).ne'⟩
    · rw [abs_of_pos (lt_of_lt_of_le hb h1)]
      exact ⟨(min_le_right _ _).trans h1, (lt_of_lt_of_le hb h1).ne'⟩
  · rw [abs_of_neg ha, abs_of_neg hb]
    rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_neg (lt_of_le_of_lt h2 hb)]
      exact ⟨(min_le_right _ _).trans (by linarith), (lt_of_le_of_lt h2 hb).ne⟩
    · rw [abs_of_neg (lt_of_le_of_lt h2 ha)]
      exact ⟨(min_le_left _ _).trans (by linarith), (lt_of_le_of_lt h2 ha).ne⟩

/-- A function with a derivative of constant sign on `[0, H]` and values of the same sign at the ends. -/
theorem mono_abs_ge {f f' : ℝ → ℝ} {H : ℝ} (hd : ∀ v, HasDerivAt f (f' v) v) {lo hi : Int}
    (hE : ∀ v ∈ Set.Icc 0 H, (lo : ℝ) ≤ f' v ∧ f' v ≤ hi) (hm : 0 < lo ∨ hi < 0) (hs : 0 < f 0 * f H) :
    ∀ v ∈ Set.Icc 0 H, min |f 0| |f H| ≤ |f v| ∧ f v ≠ 0 := by
  intro v hv
  have hH : 0 ≤ H := hv.1.trans hv.2
  have hcont : ContinuousOn f (Set.Icc 0 H) := fun w _ => (hd w).continuousAt.continuousWithinAt
  have hder : ∀ w ∈ interior (Set.Icc 0 H), HasDerivWithinAt f (f' w) (interior (Set.Icc 0 H)) w :=
    fun w _ => (hd w).hasDerivWithinAt
  have hsub : interior (Set.Icc (0 : ℝ) H) ⊆ Set.Icc 0 H := interior_subset
  apply between_abs _ hs
  rcases hm with hm | hm
  · have hl : (0 : ℝ) < lo := by exact_mod_cast hm
    have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H) hcont hder
      (fun w hw => hl.le.trans (hE w (hsub hw)).1)
    exact Or.inl ⟨hmono ⟨le_rfl, hH⟩ hv hv.1, hmono hv ⟨hH, le_rfl⟩ hv.2⟩
  · have hh : (hi : ℝ) < 0 := by exact_mod_cast hm
    have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 H) hcont hder
      (fun w hw => (hE w (hsub hw)).2.trans hh.le)
    exact Or.inr ⟨hanti hv ⟨hH, le_rfl⟩ hv.2, hanti ⟨le_rfl, hH⟩ hv hv.1⟩

/-! ## The pieces of `polyLeaf` -/

/-- The condition of `polyLeaf`: `R` has no zero on `[0, H]`. -/
def plCond (Xp Xq D : Nat) (desc : List Int) : Bool :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let R0 := encl H b
  let R1 := encl H b1
  let W0 := b.headD 0
  let Wq := evalAsc (H : Int) b
  let ex0 : Bool := decide (0 < R0.1) || decide (R0.2 < 0)
  let mono : Bool := decide (0 < R1.1) || decide (R1.2 < 0)
  ex0 || (mono && decide (0 < W0 * Wq))

/-- `sqlo - RR.2` of `polyLeaf` (a lower bound of `R'² - R R''` on `[0, H]`). -/
def plSq (Xp Xq D : Nat) (desc : List Int) : Int :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let b2 := derivAsc b1
  let R0 := encl H b
  let R1 := encl H b1
  let R2 := encl H b2
  let sq := imul R1 R1
  let sqlo : Int := if 0 ≤ R1.1 * R1.2 then max sq.1 0 else 0
  let RR := imul R0 R2
  sqlo - RR.2

/-- The slope term of `polyLeaf` for `x₀ = q`. -/
def plSlq (Xp Xq D : Nat) (desc : List Int) (cn cs : Nat) : Int :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let Wq := evalAsc (H : Int) b
  let R1H := evalAsc (H : Int) b1
  if 0 < Wq then fdiv ((cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)
  else fdiv (-(cn : Int) * R1H * (H : Int) * 2 ^ P) (Wq.natAbs * 2 ^ cs)

/-- The slope term of `polyLeaf` for `x₀ = p`. -/
def plSlp (Xp Xq D : Nat) (desc : List Int) (cn cs : Nat) : Int :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let W0 := b.headD 0
  let R10 := b1.headD 0
  if 0 < W0 then fdiv (-(cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)
  else fdiv ((cn : Int) * R10 * (H : Int) * 2 ^ P) (W0.natAbs * 2 ^ cs)

/-- The `M` part of `polyLeaf`. -/
def plMp (Xp Xq D : Nat) (desc : List Int) (cn cs : Nat) : Int :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let b2 := derivAsc b1
  let R0 := encl H b
  let R1 := encl H b1
  let R2 := encl H b2
  let W0 := b.headD 0
  let Wq := evalAsc (H : Int) b
  let ex0 : Bool := decide (0 < R0.1) || decide (R0.2 < 0)
  let mono : Bool := decide (0 < R1.1) || decide (R1.2 < 0)
  let sq := imul R1 R1
  let RR := imul R0 R2
  let Nhi : Int := sq.2 - RR.1
  let r1 : Nat := if ex0 then min R0.1.natAbs R0.2.natAbs else 0
  let rmin : Nat := if mono then max r1 (min W0.natAbs Wq.natAbs) else r1
  if 0 < Nhi then cdiv ((cn : Int) * (H : Int) * (H : Int) * Nhi * 2 ^ P) (rmin * rmin * 2 ^ cs) else 0

theorem polyLeaf_eq (tab : Nat) (l2 : Nat × Nat) (Xp Xq D : Nat) (LD : Int × Int) (x0q conv : Bool)
    (desc : List Int) (cn cs : Nat) :
    polyLeaf tab l2 Xp Xq D LD x0q conv desc cn cs =
      if plCond Xp Xq D desc then
        if conv then
          if 0 ≤ plSq Xp Xq D desc then
            if x0q then
              some (0, 0, mcLogLo tab l2 cn cs (desc.length - 1) (evalAsc ((Xq - Xp : Nat) : Int) (taylorR Xp D desc)) LD,
                plSlq Xp Xq D desc cn cs, 0)
            else
              some (0, 0, mcLogLo tab l2 cn cs (desc.length - 1) ((taylorR Xp D desc).headD 0) LD,
                plSlp Xp Xq D desc cn cs, 0)
          else none
        else
          some (mcLogLo tab l2 cn cs (desc.length - 1) ((taylorR Xp D desc).headD 0) LD,
            mcLogLo tab l2 cn cs (desc.length - 1) (evalAsc ((Xq - Xp : Nat) : Int) (taylorR Xp D desc)) LD, 0, 0,
            plMp Xp Xq D desc cn cs)
      else none := rfl


/-- `sq.2 - RR.1` of `polyLeaf` (an upper bound of `R'² - R R''` on `[0, H]`). -/
def plNhi (Xp Xq D : Nat) (desc : List Int) : Int :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let b2 := derivAsc b1
  let R0 := encl H b
  let R1 := encl H b1
  let R2 := encl H b2
  let sq := imul R1 R1
  let RR := imul R0 R2
  sq.2 - RR.1

/-- `rmin` of `polyLeaf` (a lower bound of `|R|` on `[0, H]`). -/
def plRmin (Xp Xq D : Nat) (desc : List Int) : Nat :=
  let H : Nat := Xq - Xp
  let b := taylorR Xp D desc
  let b1 := derivAsc b
  let R0 := encl H b
  let R1 := encl H b1
  let W0 := b.headD 0
  let Wq := evalAsc (H : Int) b
  let ex0 : Bool := decide (0 < R0.1) || decide (R0.2 < 0)
  let mono : Bool := decide (0 < R1.1) || decide (R1.2 < 0)
  let r1 : Nat := if ex0 then min R0.1.natAbs R0.2.natAbs else 0
  if mono then max r1 (min W0.natAbs Wq.natAbs) else r1

theorem plMp_eq (Xp Xq D : Nat) (desc : List Int) (cn cs : Nat) :
    plMp Xp Xq D desc cn cs =
      if 0 < plNhi Xp Xq D desc then
        cdiv ((cn : Int) * ((Xq - Xp : Nat) : Int) * ((Xq - Xp : Nat) : Int) * plNhi Xp Xq D desc * 2 ^ P)
          (plRmin Xp Xq D desc * plRmin Xp Xq D desc * 2 ^ cs)
      else 0 := rfl

section plSpec

variable {Xp Xq D : Nat} {desc : List Int}

theorem mem_Icc_v (hD : 0 < D) (hpq : Xp ≤ Xq) {x : ℝ} (hx : x ∈ Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D)) :
    (D : ℝ) * x - Xp ∈ Set.Icc (0 : ℝ) ((Xq - Xp : ℕ) : ℝ) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [Nat.cast_sub hpq]
  obtain ⟨h1, h2⟩ := hx
  rw [div_le_iff₀ hD'] at h1
  rw [le_div_iff₀ hD'] at h2
  constructor <;> nlinarith

theorem W0_cast (X D : Nat) (desc : List Int) :
    ((((taylorR X D desc).headD 0 : Int)) : ℝ) = evalAscR (taylorR X D desc) 0 := (evalAscR_zero _).symm

theorem evalAsc_natCast (H : Nat) (g : List Int) : ((evalAsc (H : Int) g : Int) : ℝ) = evalAscR g (H : ℝ) := by
  rw [evalAsc_spec, Int.cast_natCast]

/-- No zero of `R` on `[0, H]` under the condition of `polyLeaf`. -/
theorem plCond_R_ne_zero (hC : plCond Xp Xq D desc = true) :
    ∀ v ∈ Set.Icc (0 : ℝ) ((Xq - Xp : ℕ) : ℝ), evalAscR (taylorR Xp D desc) v ≠ 0 := by
  intro v hv
  simp only [plCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hC
  rcases hC with h0 | ⟨hm, hs⟩
  · obtain ⟨hlo, hhi⟩ := encl_spec hv.1 hv.2 (taylorR Xp D desc)
    have h := natAbs_min_le_abs hlo hhi h0
    intro hzero
    rw [hzero, abs_zero] at h
    have hpos : (0 : ℝ) < ((min (encl (Xq - Xp) (taylorR Xp D desc)).1.natAbs
        (encl (Xq - Xp) (taylorR Xp D desc)).2.natAbs : ℕ) : ℝ) := by exact_mod_cast h.2
    linarith [h.1]
  · have hs' : 0 < evalAscR (taylorR Xp D desc) 0 * evalAscR (taylorR Xp D desc) ((Xq - Xp : ℕ) : ℝ) := by
      rw [← W0_cast, ← evalAsc_natCast]
      exact_mod_cast hs
    exact (mono_abs_ge (fun w => derivAsc_spec _ w) (fun w hw => encl_spec hw.1 hw.2 _) hm hs' v hv).2

/-- **(a)**: `Q` has no zero on `[p, q]` under the condition of `polyLeaf`. -/
theorem plCond_ne_zero (hD : 0 < D) (hpq : Xp ≤ Xq) (hC : plCond Xp Xq D desc = true) :
    ∀ x ∈ Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D), (QR desc).eval x ≠ 0 := by
  intro x hx
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  rw [(eval_eq_taylor hD Xp desc x).1]
  exact div_ne_zero (plCond_R_ne_zero hC _ (mem_Icc_v hD hpq hx)) (pow_ne_zero _ hD')

theorem W0_ne_zero (hC : plCond Xp Xq D desc = true) : (taylorR Xp D desc).headD 0 ≠ 0 := by
  have h := plCond_R_ne_zero hC 0 ⟨le_rfl, Nat.cast_nonneg _⟩
  rw [← W0_cast] at h
  exact_mod_cast h

theorem Wq_ne_zero (hC : plCond Xp Xq D desc = true) :
    evalAsc ((Xq - Xp : ℕ) : Int) (taylorR Xp D desc) ≠ 0 := by
  have h := plCond_R_ne_zero hC ((Xq - Xp : ℕ) : ℝ) ⟨Nat.cast_nonneg _, le_rfl⟩
  rw [← evalAsc_natCast] at h
  exact_mod_cast h

theorem eval_p (hD : 0 < D) :
    (QR desc).eval ((Xp : ℝ) / D) = ((((taylorR Xp D desc).headD 0 : Int)) : ℝ) / D ^ (desc.length - 1) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv : (D : ℝ) * ((Xp : ℝ) / D) - Xp = 0 := by field_simp; ring
  rw [(eval_eq_taylor hD Xp desc _).1, hv, W0_cast]

theorem deval_p (hD : 0 < D) :
    (derivative (QR desc)).eval ((Xp : ℝ) / D) =
      ((((derivAsc (taylorR Xp D desc)).headD 0 : Int)) : ℝ) * D / D ^ (desc.length - 1) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv : (D : ℝ) * ((Xp : ℝ) / D) - Xp = 0 := by field_simp; ring
  rw [(eval_eq_taylor hD Xp desc _).2.1, hv, evalAscR_zero]

theorem eval_q (hD : 0 < D) (hpq : Xp ≤ Xq) :
    (QR desc).eval ((Xq : ℝ) / D) =
      ((evalAsc ((Xq - Xp : ℕ) : Int) (taylorR Xp D desc) : Int) : ℝ) / D ^ (desc.length - 1) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv : (D : ℝ) * ((Xq : ℝ) / D) - Xp = ((Xq - Xp : ℕ) : ℝ) := by rw [Nat.cast_sub hpq]; field_simp
  rw [(eval_eq_taylor hD Xp desc _).1, hv, evalAsc_natCast]

theorem deval_q (hD : 0 < D) (hpq : Xp ≤ Xq) :
    (derivative (QR desc)).eval ((Xq : ℝ) / D) =
      ((evalAsc ((Xq - Xp : ℕ) : Int) (derivAsc (taylorR Xp D desc)) : Int) : ℝ) * D / D ^ (desc.length - 1) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hv : (D : ℝ) * ((Xq : ℝ) / D) - Xp = ((Xq - Xp : ℕ) : ℝ) := by rw [Nat.cast_sub hpq]; field_simp
  rw [(eval_eq_taylor hD Xp desc _).2.1, hv, evalAsc_natCast]

theorem log_abs_div_pow {W : ℝ} (hW : W ≠ 0) {D : ℝ} (hD : 0 < D) (d : ℕ) :
    Real.log |W / D ^ d| = Real.log |W| - d * Real.log D := by
  rw [abs_div, abs_of_pos (pow_pos hD d), Real.log_div (abs_ne_zero.mpr hW) (pow_ne_zero _ hD.ne'),
    Real.log_pow]

theorem plRmin_spec (hC : plCond Xp Xq D desc = true) :
    0 < plRmin Xp Xq D desc ∧
      ∀ v ∈ Set.Icc (0 : ℝ) ((Xq - Xp : ℕ) : ℝ), (plRmin Xp Xq D desc : ℝ) ≤ |evalAscR (taylorR Xp D desc) v| := by
  have hC' := hC
  simp only [plCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hC'
  simp only [plRmin]
  set H := Xq - Xp with hH
  set b := taylorR Xp D desc with hb
  have hE0 : ∀ v ∈ Set.Icc (0 : ℝ) (H : ℝ), ((encl H b).1 : ℝ) ≤ evalAscR b v ∧ evalAscR b v ≤ (encl H b).2 :=
    fun v hv => encl_spec hv.1 hv.2 b
  have hW0 : (((b.headD 0 : ℤ)) : ℝ) = evalAscR b 0 := W0_cast _ _ _
  have hWq : ((evalAsc (H : ℤ) b : ℤ) : ℝ) = evalAscR b (H : ℝ) := evalAsc_natCast _ _
  have hH0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) H := ⟨le_rfl, Nat.cast_nonneg _⟩
  have hHH : (H : ℝ) ∈ Set.Icc (0 : ℝ) H := ⟨Nat.cast_nonneg _, le_rfl⟩
  have hex : (0 < (encl H b).1 ∨ (encl H b).2 < 0) →
      0 < min (encl H b).1.natAbs (encl H b).2.natAbs ∧
        ∀ v ∈ Set.Icc (0 : ℝ) H, ((min (encl H b).1.natAbs (encl H b).2.natAbs : ℕ) : ℝ) ≤ |evalAscR b v| :=
    fun h0 => ⟨(natAbs_min_le_abs (hE0 0 hH0).1 (hE0 0 hH0).2 h0).2,
      fun v hv => (natAbs_min_le_abs (hE0 v hv).1 (hE0 v hv).2 h0).1⟩
  have hWW : 0 < evalAscR b 0 * evalAscR b H := by
    rcases hC' with h0 | ⟨_, hs⟩
    · rcases h0 with h0 | h0
      · have hl : (0 : ℝ) < (encl H b).1 := by exact_mod_cast h0
        exact mul_pos (lt_of_lt_of_le hl (hE0 0 hH0).1) (lt_of_lt_of_le hl (hE0 H hHH).1)
      · have hh : ((encl H b).2 : ℝ) < 0 := by exact_mod_cast h0
        exact mul_pos_of_neg_of_neg (lt_of_le_of_lt (hE0 0 hH0).2 hh) (lt_of_le_of_lt (hE0 H hHH).2 hh)
    · rw [← hW0, ← hWq]
      exact_mod_cast hs
  have hmo : (0 < (encl H (derivAsc b)).1 ∨ (encl H (derivAsc b)).2 < 0) →
      0 < min (b.headD 0).natAbs (evalAsc (H : ℤ) b).natAbs ∧
        ∀ v ∈ Set.Icc (0 : ℝ) H, ((min (b.headD 0).natAbs (evalAsc (H : ℤ) b).natAbs : ℕ) : ℝ) ≤
          |evalAscR b v| := by
    intro hm
    have hmain := mono_abs_ge (fun w => derivAsc_spec b w) (fun w hw => encl_spec hw.1 hw.2 (derivAsc b)) hm hWW
    have hcast : ((min (b.headD 0).natAbs (evalAsc (H : ℤ) b).natAbs : ℕ) : ℝ) =
        min |evalAscR b 0| |evalAscR b H| := by
      rw [Nat.cast_min, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, hW0, hWq]
    refine ⟨?_, fun v hv => hcast ▸ (hmain v hv).1⟩
    have h1 : evalAscR b 0 ≠ 0 := (hmain 0 hH0).2
    have h2 : evalAscR b H ≠ 0 := (hmain H hHH).2
    have h3 : (0 : ℝ) < min |evalAscR b 0| |evalAscR b H| := lt_min (abs_pos.mpr h1) (abs_pos.mpr h2)
    rw [← hcast] at h3
    exact_mod_cast h3
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  split_ifs with hm hx hx
  · obtain ⟨a1, a2⟩ := hex hx
    obtain ⟨_, b2⟩ := hmo hm
    refine ⟨lt_of_lt_of_le a1 (le_max_left _ _), fun v hv => ?_⟩
    rw [Nat.cast_max]
    exact max_le (a2 v hv) (b2 v hv)
  · obtain ⟨b1, b2⟩ := hmo hm
    refine ⟨lt_of_lt_of_le b1 (le_max_right _ _), fun v hv => ?_⟩
    rw [Nat.cast_max, Nat.cast_zero]
    exact max_le (abs_nonneg _) (b2 v hv)
  · exact hex hx
  · exfalso
    rcases hC' with h | ⟨h, _⟩
    · exact hx h
    · exact hm h

theorem plNhi_spec : ∀ v ∈ Set.Icc (0 : ℝ) ((Xq - Xp : ℕ) : ℝ),
    (evalAscR (derivAsc (taylorR Xp D desc)) v) ^ 2 -
      evalAscR (taylorR Xp D desc) v * evalAscR (derivAsc (derivAsc (taylorR Xp D desc))) v ≤
        (plNhi Xp Xq D desc : ℝ) := by
  intro v hv
  simp only [plNhi]
  have h0 := encl_spec hv.1 hv.2 (taylorR Xp D desc)
  have h1 := encl_spec hv.1 hv.2 (derivAsc (taylorR Xp D desc))
  have h2 := encl_spec hv.1 hv.2 (derivAsc (derivAsc (taylorR Xp D desc)))
  have hsq := (imul_spec h1 h1).2
  have hRR := (imul_spec h0 h2).1
  push_cast
  rw [sq]
  linarith

theorem plSq_spec : ∀ v ∈ Set.Icc (0 : ℝ) ((Xq - Xp : ℕ) : ℝ),
    (plSq Xp Xq D desc : ℝ) ≤ (evalAscR (derivAsc (taylorR Xp D desc)) v) ^ 2 -
      evalAscR (taylorR Xp D desc) v * evalAscR (derivAsc (derivAsc (taylorR Xp D desc))) v := by
  intro v hv
  simp only [plSq]
  have h0 := encl_spec hv.1 hv.2 (taylorR Xp D desc)
  have h1 := encl_spec hv.1 hv.2 (derivAsc (taylorR Xp D desc))
  have h2 := encl_spec hv.1 hv.2 (derivAsc (derivAsc (taylorR Xp D desc)))
  have hsq := (imul_spec h1 h1).1
  have hRR := (imul_spec h0 h2).2
  have hpos := sq_nonneg (evalAscR (derivAsc (taylorR Xp D desc)) v)
  split_ifs
  · push_cast
    rw [sq] at hpos ⊢
    have : (max ((imul (encl (Xq - Xp) (derivAsc (taylorR Xp D desc)))
        (encl (Xq - Xp) (derivAsc (taylorR Xp D desc)))).1 : ℝ) 0) ≤
        evalAscR (derivAsc (taylorR Xp D desc)) v * evalAscR (derivAsc (taylorR Xp D desc)) v :=
      max_le hsq hpos
    linarith
  · push_cast
    linarith

/-- **(b), the `M` part.** -/
theorem plMp_spec (hD : 0 < D) (hpq : Xp ≤ Xq) (hC : plCond Xp Xq D desc = true) (cn cs : ℕ) :
    0 ≤ plMp Xp Xq D desc cn cs ∧
    ∀ x ∈ Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D),
      (cn : ℝ) / 2 ^ cs * (((derivative (QR desc)).eval x) ^ 2 -
        (QR desc).eval x * (derivative (derivative (QR desc))).eval x) / ((QR desc).eval x) ^ 2 *
        ((Xq : ℝ) / D - Xp / D) ^ 2 ≤ (plMp Xp Xq D desc cn cs : ℝ) / 2 ^ P := by
  obtain ⟨hr0, hr⟩ := plRmin_spec hC
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hcs : (0 : ℝ) < 2 ^ cs := by positivity
  have hden : 0 < plRmin Xp Xq D desc * plRmin Xp Xq D desc * 2 ^ cs := by positivity
  rw [plMp_eq]
  constructor
  · split_ifs with hN
    · have h1 := le_cdiv ((cn : Int) * ((Xq - Xp : Nat) : Int) * ((Xq - Xp : Nat) : Int) *
        plNhi Xp Xq D desc * 2 ^ P) hden
      have hNr : (0 : ℝ) < plNhi Xp Xq D desc := by exact_mod_cast hN
      have h2 : (0 : ℝ) ≤ (((cn : Int) * ((Xq - Xp : Nat) : Int) * ((Xq - Xp : Nat) : Int) *
          plNhi Xp Xq D desc * 2 ^ P : Int) : ℝ) / ((plRmin Xp Xq D desc * plRmin Xp Xq D desc * 2 ^ cs : ℕ) : ℝ) := by
        apply div_nonneg _ (Nat.cast_nonneg _)
        push_cast
        positivity
      exact_mod_cast h2.trans h1
    · exact le_rfl
  · intro x hx
    have hv := mem_Icc_v hD hpq hx
    obtain ⟨e0, e1, e2⟩ := eval_eq_taylor hD Xp desc x
    have hRne := plCond_R_ne_zero hC _ hv
    have hK := plNhi_spec (D := D) (desc := desc) _ hv
    have hrv := hr _ hv
    have hpow : (D : ℝ) ^ (desc.length - 1) ≠ 0 := pow_ne_zero _ hD'.ne'
    have hHr : ((Xq : ℝ) / D - Xp / D) = ((Xq - Xp : ℕ) : ℝ) / D := by
      rw [Nat.cast_sub hpq]
      field_simp
    set Rv := evalAscR (taylorR Xp D desc) ((D : ℝ) * x - Xp) with hRv
    set R1v := evalAscR (derivAsc (taylorR Xp D desc)) ((D : ℝ) * x - Xp) with hR1v
    set R2v := evalAscR (derivAsc (derivAsc (taylorR Xp D desc))) ((D : ℝ) * x - Xp) with hR2v
    set Hr : ℝ := ((Xq - Xp : ℕ) : ℝ) with hHr_def
    have hLHS : (cn : ℝ) / 2 ^ cs * (((derivative (QR desc)).eval x) ^ 2 -
        (QR desc).eval x * (derivative (derivative (QR desc))).eval x) / ((QR desc).eval x) ^ 2 *
        ((Xq : ℝ) / D - Xp / D) ^ 2 = (cn : ℝ) / 2 ^ cs * ((R1v ^ 2 - Rv * R2v) / Rv ^ 2) * Hr ^ 2 := by
      rw [e0, e1, e2, hHr]
      field_simp
    rw [hLHS]
    have hRv2 : ((plRmin Xp Xq D desc : ℕ) : ℝ) ^ 2 ≤ Rv ^ 2 := by
      have h := mul_self_le_mul_self (Nat.cast_nonneg _) hrv
      rw [← sq, ← sq, sq_abs] at h
      exact h
    have hRvpos : 0 < Rv ^ 2 := by positivity
    have hc0 : (0 : ℝ) ≤ (cn : ℝ) / 2 ^ cs := by positivity
    split_ifs with hN
    · have hlow := le_cdiv ((cn : Int) * ((Xq - Xp : Nat) : Int) * ((Xq - Xp : Nat) : Int) *
        plNhi Xp Xq D desc * 2 ^ P) hden
      rw [le_div_iff₀ hP]
      refine le_trans ?_ hlow
      have hNr : (0 : ℝ) < plNhi Xp Xq D desc := by exact_mod_cast hN
      have hrr : (0 : ℝ) < (plRmin Xp Xq D desc : ℝ) := by exact_mod_cast hr0
      have step1 : (R1v ^ 2 - Rv * R2v) / Rv ^ 2 ≤ (plNhi Xp Xq D desc : ℝ) / (plRmin Xp Xq D desc : ℝ) ^ 2 :=
        calc (R1v ^ 2 - Rv * R2v) / Rv ^ 2 ≤ (plNhi Xp Xq D desc : ℝ) / Rv ^ 2 :=
              div_le_div_of_nonneg_right hK hRvpos.le
          _ ≤ (plNhi Xp Xq D desc : ℝ) / (plRmin Xp Xq D desc : ℝ) ^ 2 :=
              div_le_div_of_nonneg_left hNr.le (by positivity) hRv2
      have e : ((((cn : Int) * ((Xq - Xp : Nat) : Int) * ((Xq - Xp : Nat) : Int) *
          plNhi Xp Xq D desc * 2 ^ P : Int) : ℝ) / ((plRmin Xp Xq D desc * plRmin Xp Xq D desc * 2 ^ cs : ℕ) : ℝ)) =
          (cn : ℝ) / 2 ^ cs * ((plNhi Xp Xq D desc : ℝ) / (plRmin Xp Xq D desc : ℝ) ^ 2) * Hr ^ 2 * 2 ^ P := by
        rw [hHr_def]
        push_cast
        field_simp
      rw [e]
      have := mul_le_mul_of_nonneg_left step1 hc0
      have := mul_le_mul_of_nonneg_right this (sq_nonneg Hr)
      exact mul_le_mul_of_nonneg_right this hP.le
    · have hNr : (plNhi Xp Xq D desc : ℝ) ≤ 0 := by exact_mod_cast not_lt.mp hN
      have hK0 : (R1v ^ 2 - Rv * R2v) / Rv ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (hK.trans hNr) hRvpos.le
      rw [Int.cast_zero, zero_div]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc0 hK0) (sq_nonneg _)

/-- **(c), convexity.** -/
theorem plSq_convexOn (hD : 0 < D) (hpq : Xp ≤ Xq) (hC : plCond Xp Xq D desc = true)
    (hsq : 0 ≤ plSq Xp Xq D desc) {c : ℝ} (hc : 0 ≤ c) :
    ConvexOn ℝ (Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D)) (fun x => -c * Real.log |(QR desc).eval x|) := by
  have hne := plCond_ne_zero hD hpq hC
  have hint : interior (Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D)) = Set.Ioo ((Xp : ℝ) / D) ((Xq : ℝ) / D) :=
    interior_Icc
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (f' := fun x => -c * ((derivative (QR desc)).eval x / (QR desc).eval x))
    (f'' := fun x => c * ((derivative (QR desc)).eval x ^ 2 -
      (QR desc).eval x * (derivative (derivative (QR desc))).eval x) / ((QR desc).eval x) ^ 2) ?_ ?_ ?_ ?_
  · exact fun x hx => (hasDerivAt_neg_mul_log_abs_eval _ c (hne x hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [hint] at hx
    exact (hasDerivAt_neg_mul_log_abs_eval _ c (hne x (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    exact (hasDerivAt_neg_mul_logDeriv_eval _ c (hne x (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    have hxI := Set.Ioo_subset_Icc_self hx
    have hv := mem_Icc_v hD hpq hxI
    obtain ⟨e0, e1, e2⟩ := eval_eq_taylor hD Xp desc x
    have hS := plSq_spec (D := D) (desc := desc) _ hv
    have hS0 : (0 : ℝ) ≤ (plSq Xp Xq D desc : ℝ) := by exact_mod_cast hsq
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    have hpow : (0 : ℝ) < (D : ℝ) ^ (desc.length - 1) := by positivity
    have key : 0 ≤ (derivative (QR desc)).eval x ^ 2 -
        (QR desc).eval x * (derivative (derivative (QR desc))).eval x := by
      rw [e0, e1, e2]
      set Rv := evalAscR (taylorR Xp D desc) ((D : ℝ) * x - Xp)
      set R1v := evalAscR (derivAsc (taylorR Xp D desc)) ((D : ℝ) * x - Xp)
      set R2v := evalAscR (derivAsc (derivAsc (taylorR Xp D desc))) ((D : ℝ) * x - Xp)
      have e : (R1v * D / (D : ℝ) ^ (desc.length - 1)) ^ 2 - Rv / (D : ℝ) ^ (desc.length - 1) *
          (R2v * D ^ 2 / (D : ℝ) ^ (desc.length - 1)) =
          ((D : ℝ) / (D : ℝ) ^ (desc.length - 1)) ^ 2 * (R1v ^ 2 - Rv * R2v) := by
        field_simp
      rw [e]
      exact mul_nonneg (sq_nonneg _) (hS0.trans hS)
    exact div_nonneg (mul_nonneg hc key) (sq_nonneg _)

/-- **(c), the slope term at `x₀ = q`.** -/
theorem plSlq_spec (hD : 0 < D) (hpq : Xp ≤ Xq) (hC : plCond Xp Xq D desc = true) (cn cs : ℕ) :
    (plSlq Xp Xq D desc cn cs : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) *
      ((derivative (QR desc)).eval ((Xq : ℝ) / D) / (QR desc).eval ((Xq : ℝ) / D))) * ((Xp : ℝ) / D - Xq / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hpow : (D : ℝ) ^ (desc.length - 1) ≠ 0 := pow_ne_zero _ hD'.ne'
  have hWq0 := Wq_ne_zero hC
  rw [eval_q hD hpq, deval_q hD hpq]
  simp only [plSlq]
  set Wq := evalAsc ((Xq - Xp : ℕ) : Int) (taylorR Xp D desc) with hWq
  set R1H := evalAsc ((Xq - Xp : ℕ) : Int) (derivAsc (taylorR Xp D desc)) with hR1H
  have hWqr : (Wq : ℝ) ≠ 0 := by exact_mod_cast hWq0
  have hHr : (Xp : ℝ) / D - Xq / D = -(((Xq - Xp : ℕ) : ℝ) / D) := by
    rw [Nat.cast_sub hpq]
    field_simp
    ring
  have hRHS : 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (((R1H : ℝ) * D / (D : ℝ) ^ (desc.length - 1)) /
      ((Wq : ℝ) / (D : ℝ) ^ (desc.length - 1)))) * ((Xp : ℝ) / D - Xq / D) =
      (cn : ℝ) * R1H * ((Xq - Xp : ℕ) : ℝ) * 2 ^ P / (Wq * 2 ^ cs) := by
    rw [hHr]
    field_simp
  rw [hRHS]
  have hden : 0 < Wq.natAbs * 2 ^ cs := Nat.mul_pos (Int.natAbs_pos.mpr hWq0) (by positivity)
  have hcast : ((Wq.natAbs * 2 ^ cs : ℕ) : ℝ) = |(Wq : ℝ)| * 2 ^ cs := by
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs with hpos
  · have h := fdiv_le ((cn : Int) * R1H * ((Xq - Xp : ℕ) : Int) * 2 ^ P) hden
    rw [hcast, abs_of_pos (by exact_mod_cast hpos : (0 : ℝ) < Wq)] at h
    push_cast at h
    exact h
  · have hneg : (Wq : ℝ) < 0 := by
      have : Wq < 0 := lt_of_le_of_ne (not_lt.mp hpos) hWq0
      exact_mod_cast this
    have h := fdiv_le (-(cn : Int) * R1H * ((Xq - Xp : ℕ) : Int) * 2 ^ P) hden
    rw [hcast, abs_of_neg hneg] at h
    push_cast at h
    refine h.trans (le_of_eq ?_)
    field_simp

/-- **(c), the slope term at `x₀ = p`.** -/
theorem plSlp_spec (hD : 0 < D) (hpq : Xp ≤ Xq) (hC : plCond Xp Xq D desc = true) (cn cs : ℕ) :
    (plSlp Xp Xq D desc cn cs : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) *
      ((derivative (QR desc)).eval ((Xp : ℝ) / D) / (QR desc).eval ((Xp : ℝ) / D))) * ((Xq : ℝ) / D - Xp / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hpow : (D : ℝ) ^ (desc.length - 1) ≠ 0 := pow_ne_zero _ hD'.ne'
  have hW00 := W0_ne_zero hC
  rw [eval_p hD, deval_p hD]
  simp only [plSlp]
  set W0 := (taylorR Xp D desc).headD 0 with hW0
  set R10 := (derivAsc (taylorR Xp D desc)).headD 0 with hR10
  have hW0r : (W0 : ℝ) ≠ 0 := by exact_mod_cast hW00
  have hHr : (Xq : ℝ) / D - Xp / D = ((Xq - Xp : ℕ) : ℝ) / D := by
    rw [Nat.cast_sub hpq]
    field_simp
  have hRHS : 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * (((R10 : ℝ) * D / (D : ℝ) ^ (desc.length - 1)) /
      ((W0 : ℝ) / (D : ℝ) ^ (desc.length - 1)))) * ((Xq : ℝ) / D - Xp / D) =
      -(cn : ℝ) * R10 * ((Xq - Xp : ℕ) : ℝ) * 2 ^ P / (W0 * 2 ^ cs) := by
    rw [hHr]
    field_simp
  rw [hRHS]
  have hden : 0 < W0.natAbs * 2 ^ cs := Nat.mul_pos (Int.natAbs_pos.mpr hW00) (by positivity)
  have hcast : ((W0.natAbs * 2 ^ cs : ℕ) : ℝ) = |(W0 : ℝ)| * 2 ^ cs := by
    push_cast
    rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs with hpos
  · have h := fdiv_le (-(cn : Int) * R10 * ((Xq - Xp : ℕ) : Int) * 2 ^ P) hden
    rw [hcast, abs_of_pos (by exact_mod_cast hpos : (0 : ℝ) < W0)] at h
    push_cast at h
    exact h
  · have hneg : (W0 : ℝ) < 0 := by
      have : W0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) hW00
      exact_mod_cast this
    have h := fdiv_le ((cn : Int) * R10 * ((Xq - Xp : ℕ) : Int) * 2 ^ P) hden
    rw [hcast, abs_of_neg hneg] at h
    push_cast at h
    refine h.trans (le_of_eq ?_)
    field_simp

end plSpec


/-! ## The semantics of `polyLeaf` -/

section polyLeafSpec

variable {tab : Nat} {l2 : Nat × Nat} {Xp Xq D : Nat} {LD : Int × Int} {x0q conv : Bool}
  {desc : List Int} {cn cs : Nat} {ap aq t0 sl mp : Int}

theorem polyLeaf_cond (h : polyLeaf tab l2 Xp Xq D LD x0q conv desc cn cs = some (ap, aq, t0, sl, mp)) :
    plCond Xp Xq D desc = true := by
  rw [polyLeaf_eq] at h
  by_contra hC
  rw [ite_eq_right hC] at h
  exact absurd h (by simp)

/-- **`polyLeaf` (a)**: `Q` has no zero on `[p, q]`. -/
theorem polyLeaf_eval_ne_zero (hD : 0 < D) (hpq : Xp < Xq)
    (h : polyLeaf tab l2 Xp Xq D LD x0q conv desc cn cs = some (ap, aq, t0, sl, mp)) :
    ∀ x ∈ Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D), (QR desc).eval x ≠ 0 :=
  plCond_ne_zero hD hpq.le (polyLeaf_cond h)

/-- **`polyLeaf` (b)**, `conv = false`: lower bounds of `2^P (-c log |Q|)` at `p` and `q`, `t0 = sl = 0`, and the
`M` part: `c (Q'² - Q Q'') / Q² · (q - p)² ≤ mp / 2^P` on `[p, q]`, with `c = cn / 2^cs`. -/
theorem polyLeaf_noconv
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2)
    (hD : 0 < D) (hpq : Xp < Xq)
    (h : polyLeaf tab l2 Xp Xq D LD x0q conv desc cn cs = some (ap, aq, t0, sl, mp)) (hc : conv = false) :
    (ap : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval ((Xp : ℝ) / D)|) ∧
    (aq : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval ((Xq : ℝ) / D)|) ∧
    t0 = 0 ∧ sl = 0 ∧ 0 ≤ mp ∧
    ∀ x ∈ Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D),
      (cn : ℝ) / 2 ^ cs * (((derivative (QR desc)).eval x) ^ 2 -
        (QR desc).eval x * (derivative (derivative (QR desc))).eval x) / ((QR desc).eval x) ^ 2 *
        ((Xq : ℝ) / D - Xp / D) ^ 2 ≤ (mp : ℝ) / 2 ^ P := by
  have hC := polyLeaf_cond h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [polyLeaf_eq, ite_eq_left hC] at h
  subst hc
  simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  have hW0 := W0_ne_zero hC
  have hWq := Wq_ne_zero hC
  obtain ⟨hm0, hm⟩ := plMp_spec hD hpq.le hC cn cs
  refine ⟨?_, ?_, rfl, rfl, hm0, hm⟩
  · rw [eval_p hD, log_abs_div_pow (by exact_mod_cast hW0) hD']
    exact mcLogLo_le hlog hLD hW0 cn cs _
  · rw [eval_q hD hpq.le, log_abs_div_pow (by exact_mod_cast hWq) hD']
    exact mcLogLo_le hlog hLD hWq cn cs _

/-- **`polyLeaf` (c)**, `conv = true`: `ap = aq = mp = 0`, `x ↦ -c log |Q x|` is convex on `[p, q]`, and with
`x₀ = if x0q then q else p`, `x_f = if x0q then p else q`: `t0 ≤ 2^P (-c log |Q x₀|)` and
`sl ≤ 2^P (-c Q'(x₀)/Q(x₀)) (x_f - x₀)`. -/
theorem polyLeaf_conv
    (hlog : ∀ a b : ℕ, 0 < a → 0 < b → ((logT tab l2 a b).1 : ℝ) ≤ 2 ^ P * Real.log (a / b) ∧
      2 ^ P * Real.log (a / b) ≤ (logT tab l2 a b).2)
    (hLD : (LD.1 : ℝ) ≤ 2 ^ P * Real.log D ∧ 2 ^ P * Real.log D ≤ LD.2)
    (hD : 0 < D) (hpq : Xp < Xq)
    (h : polyLeaf tab l2 Xp Xq D LD x0q conv desc cn cs = some (ap, aq, t0, sl, mp)) (hc : conv = true) :
    ap = 0 ∧ aq = 0 ∧ mp = 0 ∧
    ConvexOn ℝ (Set.Icc ((Xp : ℝ) / D) ((Xq : ℝ) / D))
      (fun x => -((cn : ℝ) / 2 ^ cs) * Real.log |(QR desc).eval x|) ∧
    (t0 : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) *
      Real.log |(QR desc).eval (if x0q then (Xq : ℝ) / D else (Xp : ℝ) / D)|) ∧
    (sl : ℝ) ≤ 2 ^ P * (-((cn : ℝ) / 2 ^ cs) *
      ((derivative (QR desc)).eval (if x0q then (Xq : ℝ) / D else (Xp : ℝ) / D) /
        (QR desc).eval (if x0q then (Xq : ℝ) / D else (Xp : ℝ) / D))) *
      ((if x0q then (Xp : ℝ) / D else (Xq : ℝ) / D) - (if x0q then (Xq : ℝ) / D else (Xp : ℝ) / D)) := by
  have hC := polyLeaf_cond h
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  rw [polyLeaf_eq, ite_eq_left hC] at h
  subst hc
  simp only [↓reduceIte] at h
  by_cases hsq : 0 ≤ plSq Xp Xq D desc
  · rw [ite_eq_left hsq] at h
    have hconv := plSq_convexOn hD hpq.le hC hsq (c := (cn : ℝ) / 2 ^ cs) (by positivity)
    have hW0 := W0_ne_zero hC
    have hWq := Wq_ne_zero hC
    cases x0q
    · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, hconv, ?_, plSlp_spec hD hpq.le hC cn cs⟩
      rw [eval_p hD, log_abs_div_pow (by exact_mod_cast hW0) hD']
      exact mcLogLo_le hlog hLD hW0 cn cs _
    · simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, hconv, ?_, plSlq_spec hD hpq.le hC cn cs⟩
      rw [eval_q hD hpq.le, log_abs_div_pow (by exact_mod_cast hWq) hD']
      exact mcLogLo_le hlog hLD hWq cn cs _
  · rw [ite_eq_right hsq] at h
    exact absurd h (by simp)

end polyLeafSpec

end TPMahler.Cert
