import TPMahler.CheckSound9
import TPMahler.Assembly

/-!
# The certificate as an instance of `CertHyp`

`certHyp_of`: the degree condition `∑ cⱼ deg Qⱼ + 2s < 1` and the auxiliary inequality `FR x ≥ 0` (for `x > 0` off the
roots of the `Qⱼ`) give `CertHyp Qc cR m0 NN eR GR sR`. The data conditions come from `TPMahler.TailSound`; here we add
the degrees of the `Qⱼ` (leading coefficients are nonzero) and the bridge `‖Qⱼ(x)‖ = |Qⱼ(x)|` for real `x`.
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-! ## Horner polynomials: degree and nonvanishing -/

theorem foldl_horner_shift (t : List ℤ) (p : ℤ[X]) :
    t.foldl (fun acc a => acc * X + Polynomial.C a) p =
      p * X ^ t.length + t.foldl (fun acc a => acc * X + Polynomial.C a) 0 := by
  induction t generalizing p with
  | nil => simp
  | cons b t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (p * X + Polynomial.C b), ih (0 * X + Polynomial.C b)]
    ring

theorem Qd_cons (b : ℤ) (t : List ℤ) : Qd (b :: t) = Polynomial.C b * X ^ t.length + Qd t := by
  unfold Qd
  rw [List.foldl_cons, foldl_horner_shift]
  ring

theorem degree_Qd_lt (t : List ℤ) : (Qd t).degree < t.length := by
  induction t with
  | nil => simp [Qd]
  | cons b t ih =>
    rw [Qd_cons, List.length_cons]
    calc (Polynomial.C b * X ^ t.length + Qd t).degree
        ≤ max (Polynomial.C b * X ^ t.length).degree (Qd t).degree := degree_add_le _ _
      _ < ((t.length + 1 : ℕ) : WithBot ℕ) := by
        apply max_lt
        · exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast Nat.lt_succ_self _)
        · exact lt_trans ih (by exact_mod_cast Nat.lt_succ_self _)

theorem degree_Qd_lt_lead {b : ℤ} (hb : b ≠ 0) (t : List ℤ) :
    (Qd t).degree < (Polynomial.C b * X ^ t.length).degree := by
  rw [degree_C_mul_X_pow t.length hb]
  exact degree_Qd_lt t

theorem natDegree_Qd_cons {b : ℤ} (hb : b ≠ 0) (t : List ℤ) : (Qd (b :: t)).natDegree = t.length := by
  rw [Qd_cons, natDegree_add_eq_left_of_degree_lt (degree_Qd_lt_lead hb t),
    natDegree_C_mul_X_pow t.length b hb]

theorem Qd_cons_ne_zero {b : ℤ} (hb : b ≠ 0) (t : List ℤ) : Qd (b :: t) ≠ 0 := by
  intro h
  have hdeg := congrArg degree h
  rw [Qd_cons, degree_add_eq_left_of_degree_lt (degree_Qd_lt_lead hb t), degree_C_mul_X_pow t.length hb,
    degree_zero] at hdeg
  exact WithBot.coe_ne_bot hdeg

/-! ## The certificate polynomials -/

/-- Every certificate polynomial has a nonzero leading coefficient (kernel reduction on the data). -/
theorem polys_ok : ∀ j < 19, polys.getD j [] ≠ [] ∧ (polys.getD j []).headD 0 ≠ 0 := by
  decide +kernel

theorem natDegree_Qc (j : Fin JJ) : (Qc j).natDegree = (polys.getD j []).length - 1 := by
  obtain ⟨hne, hhead⟩ := polys_ok j j.isLt
  unfold Qc
  generalize polys.getD (↑j) [] = l at hne hhead ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    rw [List.headD_cons] at hhead
    rw [natDegree_Qd_cons hhead, List.length_cons, Nat.add_sub_cancel]

theorem Qc_ne_zero (j : Fin JJ) : Qc j ≠ 0 := by
  obtain ⟨hne, hhead⟩ := polys_ok j j.isLt
  unfold Qc
  generalize polys.getD (↑j) [] = l at hne hhead ⊢
  cases l with
  | nil => exact absurd rfl hne
  | cons b t =>
    rw [List.headD_cons] at hhead
    exact Qd_cons_ne_zero hhead t

theorem cR_eq_cj (j : Fin JJ) : cR j = cj j := rfl

theorem cR_nonneg (j : Fin JJ) : 0 ≤ cR j := by
  unfold cR
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem sum_cR_natDegree :
    ∑ j : Fin JJ, cR j * ((Qc j).natDegree : ℝ) =
      ∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) := by
  have h := Fin.sum_univ_eq_sum_range (fun j => cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ)) JJ
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [natDegree_Qc, cR_eq_cj]

theorem norm_eval_toC_Qc (j : Fin JJ) (x : ℝ) :
    ‖eval (x : ℂ) (toC (Qc j))‖ = |(QR (polys.getD j [])).eval x| := by
  unfold Qc
  exact toC_eval_eq (polys.getD j []) x

/-- **The certificate gives `CertHyp`.** -/
theorem certHyp_of
    (hbud : ∑ j ∈ Finset.range 19, cj j * (((polys.getD j []).length - 1 : ℕ) : ℝ) + 2 * sR < 1)
    (hF : ∀ x : ℝ, 0 < x → (∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0) → 0 ≤ FR x) :
    CertHyp Qc cR m0 NN eR GR sR where
  Q_ne_zero := Qc_ne_zero
  c_nonneg := cR_nonneg
  nodes := eR_lt
  G_nonneg := fun k _ => GR_nonneg k
  G_first := GR_zero
  G_last := GR_NN
  mass := sR_eq_trapezoid.symm
  mass_pos := sR_pos
  budget := by
    rw [sum_cR_natDegree]
    exact hbud.le
  F_nonneg := by
    intro x hx hQx
    have hQ' : ∀ j < 19, (QR (polys.getD j [])).eval x ≠ 0 := by
      intro j hj h0
      apply hQx ⟨j, hj⟩
      have h1 := norm_eval_toC_Qc ⟨j, hj⟩ x
      have h2 : |(QR (polys.getD (↑(⟨j, hj⟩ : Fin JJ)) [])).eval x| = 0 := by
        show |(QR (polys.getD j [])).eval x| = 0
        rw [h0, abs_zero]
      rw [h2] at h1
      exact norm_eq_zero.mp h1
    have h := hF x hx hQ'
    have hsum : ∑ j : Fin JJ, cR j * Real.log ‖eval (x : ℂ) (toC (Qc j))‖ =
        ∑ j : Fin JJ, cR j * Real.log |(QR (polys.getD j [])).eval x| :=
      Finset.sum_congr rfl (fun j _ => by rw [norm_eval_toC_Qc])
    rw [hsum]
    unfold FR UR IR CR at h
    exact h

end TPMahler.Cert
