import TPMahler.CheckSound9

/-!
# Soundness of the energy check: `energy_sound`

`IR = ∑ᵢ ∑ₖ Cᵢ Cₖ L(eᵢ - eₖ) = 2 ∑_{i<k} Cᵢ Cₖ L(eₖ - eᵢ) = (1 / (12 · 10^40)) ∑_{i<k} Cᵢ Cₖ V_ik` with
`V_ik = d⁴ (log d - log 10^10 - 25/12)`, `d = nₖ - nᵢ`; `iBlock 0 5473` encloses `2^300 ∑_{i<k} Cᵢ Cₖ V_ik`
(records at scale `2^QI`, logarithms at scale `2^PI`, `QI = PI = 100`).
-/

open Polynomial

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-! ## Tables and logarithms at precision `PI` -/

theorem tabI_check : tableCheck 100 24 48 TABI 102 = true := by decide +kernel

theorem l2I_check : l2Check 100 24 48 L2I.1 L2I.2 = true := by decide +kernel

theorem tabI_ok : TableOK PI TABI WI := tableCheck_sound tabI_check

theorem l2I_ok : ((L2I.1 : ℕ) : ℝ) ≤ 2 ^ PI * Real.log 2 ∧ 2 ^ PI * Real.log 2 ≤ ((L2I.2 : ℕ) : ℝ) :=
  l2Check_sound l2I_check

theorem logI_sound {tab : ℕ} {l2 : ℕ × ℕ} (hT : TableOK PI tab WI)
    (hl2 : ((l2.1 : ℕ) : ℝ) ≤ 2 ^ PI * Real.log 2 ∧ 2 ^ PI * Real.log 2 ≤ ((l2.2 : ℕ) : ℝ))
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((logI tab l2 a b).1 : ℝ) ≤ 2 ^ PI * Real.log ((a : ℝ) / b) ∧
      2 ^ PI * Real.log ((a : ℝ) / b) ≤ ((logI tab l2 a b).2 : ℝ) := by
  unfold logI
  refine logK_sound ha hb hT ?_ ?_
  · have := hl2.1
    simpa using this
  · have := hl2.2
    simpa using this

/-! ## Node records at scale `2^q` -/

/-- The intended record of node `i` at scale `2^q`. -/
def recOfQ (q i : ℕ) : NRec :=
  ⟨nodes.getD i 0, Int.sign (recNum i), fdiv (recNum i * 2 ^ q) (recDen i), cdiv (recNum i * 2 ^ q) (recDen i)⟩

theorem mkRecsAux_eqQ (q : ℕ) : ∀ k j : ℕ, j + k = NN →
    mkRecsAux q GS (pnOf j) (pdOf j) (nodes.drop j) (gvals.drop j) = (List.range' j (k + 1)).map (recOfQ q) := by
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
    simp only [mkRecsAux, pnOf, pdOf, ite_eq_right hNN, recOfQ, recNum, recDen, lt_irrefl, ite_false]
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
    · have hjN : j < NN := by omega
      by_cases hj0 : j = 0
      · subst hj0
        simp [recOfQ, recNum, recDen, pnOf, pdOf, snI, sdI]
      · simp [recOfQ, recNum, recDen, pnOf, pdOf, snI, sdI, hj0, hjN]
    · rw [show ((↑(gvals.getD (j + 1) 0) : ℤ) - ↑(gvals.getD j 0)) * (DEC : ℤ) = pnOf (j + 1) from hpn,
        show (nodes.getD (j + 1) 0 - nodes.getD j 0) * 2 ^ GS = pdOf (j + 1) from hpd]
      exact hrest

theorem recsI_eq : recsI = (List.range (NN + 1)).map (recOfQ QI) := by
  have h := mkRecsAux_eqQ QI NN 0 (by simp)
  simp only [pnOf, pdOf, List.drop_zero] at h
  unfold recsI
  rw [List.range_eq_range']
  exact h

/-- The record of node `i` at scale `2^q` encloses `2^q C_i`, and its sign field vanishes iff `C_i = 0`. -/
theorem recOfQ_spec (q : ℕ) {i : ℕ} (hi : i ≤ NN) :
    ((recOfQ q i).clo : ℝ) ≤ 2 ^ q * CR i ∧ 2 ^ q * CR i ≤ ((recOfQ q i).chi : ℝ) ∧
      ((recOfQ q i).sg = 0 → CR i = 0) := by
  have hd := recDen_pos hi
  have hdR : (0 : ℝ) < recDen i := by exact_mod_cast hd
  have hC := recNum_div hi
  refine ⟨?_, ?_, ?_⟩
  · have := fdiv_le (recNum i * 2 ^ q) hd
    show ((fdiv (recNum i * 2 ^ q) (recDen i) : ℤ) : ℝ) ≤ _
    rw [← hC]
    push_cast at this
    calc _ ≤ ((recNum i : ℝ) * 2 ^ q) / recDen i := this
      _ = 2 ^ q * ((recNum i : ℝ) / recDen i) := by ring
  · have := le_cdiv (recNum i * 2 ^ q) hd
    show _ ≤ ((cdiv (recNum i * 2 ^ q) (recDen i) : ℤ) : ℝ)
    rw [← hC]
    push_cast at this
    calc 2 ^ q * ((recNum i : ℝ) / recDen i) = ((recNum i : ℝ) * 2 ^ q) / recDen i := by ring
      _ ≤ _ := this
  · show Int.sign (recNum i) = 0 → CR i = 0
    rw [Int.sign_eq_zero_iff_zero, ← hC]
    intro h
    rw [h]
    simp

theorem recOfQ_n (q i : ℕ) : (recOfQ q i).n = nodes.getD i 0 := rfl

/-! ## Enclosure of the energy blocks -/

/-- `V(d) = d⁴ (log d - log 10^10 - 25/12)`. -/
noncomputable def Vd (d : ℕ) : ℝ := (d : ℝ) ^ 4 * (Real.log d - Real.log DEC - 25 / 12)

/-- A record enclosing `2^QI c`, with sign field `0` only if `c = 0`. -/
def RecSpecI (r : NRec) (c : ℝ) : Prop :=
  (r.clo : ℝ) ≤ 2 ^ QI * c ∧ 2 ^ QI * c ≤ r.chi ∧ (r.sg = 0 → c = 0)

theorem foldl_fst_le {α : Type*} (f : ℤ × ℤ → α → ℤ × ℤ) (g : α → ℝ) (P : α → Prop)
    (hf : ∀ acc x, P x → ((f acc x).1 : ℝ) ≤ acc.1 + g x) :
    ∀ (l : List α) (acc : ℤ × ℤ), (∀ x ∈ l, P x) → ((l.foldl f acc).1 : ℝ) ≤ acc.1 + (l.map g).sum := by
  intro l
  induction l with
  | nil =>
    intro acc _
    simp
  | cons x l ih =>
    intro acc hl
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have h1 := hf acc x (hl x (by simp))
    have h2 := ih (f acc x) (fun y hy => hl y (List.mem_cons_of_mem x hy))
    linarith

/-- The third factor of a term of `iRow`: enclosure of `2^PI V(d)`. -/
def thirdI (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (d : ℕ) : ℤ × ℤ :=
  let L := logI tab l2 d 1
  let d4 : ℤ := ((d * d) * (d * d) : ℕ)
  (d4 * (L.1 - lDec.2 - cdiv (25 * 2 ^ PI) 12), d4 * (L.2 - lDec.1 - fdiv (25 * 2 ^ PI) 12))

/-- One step of the fold in `iRow`. -/
def iRowStep (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (ri : NRec) (acc : ℤ × ℤ) (rk : NRec) : ℤ × ℤ :=
  if rk.sg = 0 then acc else
  let t := imul (imul (ri.clo, ri.chi) (rk.clo, rk.chi)) (thirdI tab l2 lDec (rk.n - ri.n))
  (acc.1 + t.1, acc.2 + t.2)

theorem iRow_eq (tab : ℕ) (l2 : ℕ × ℕ) (lDec : ℤ × ℤ) (ri : NRec) (rest : List NRec) :
    iRow tab l2 lDec ri rest = rest.foldl (iRowStep tab l2 lDec ri) (0, 0) := rfl

section encl

variable {tab : ℕ} {l2 : ℕ × ℕ} {lDec : ℤ × ℤ} (hT : TableOK PI tab WI)
  (hl2 : ((l2.1 : ℕ) : ℝ) ≤ 2 ^ PI * Real.log 2 ∧ 2 ^ PI * Real.log 2 ≤ ((l2.2 : ℕ) : ℝ))
  (hDec : (lDec.1 : ℝ) ≤ 2 ^ PI * Real.log DEC ∧ 2 ^ PI * Real.log DEC ≤ lDec.2)
include hT hl2 hDec

theorem thirdI_encl (d : ℕ) :
    ((thirdI tab l2 lDec d).1 : ℝ) ≤ 2 ^ PI * Vd d ∧ 2 ^ PI * Vd d ≤ ((thirdI tab l2 lDec d).2 : ℝ) := by
  have hc1 := fdiv_le (25 * 2 ^ PI) (b := 12) (by norm_num)
  have hc2 := le_cdiv (25 * 2 ^ PI) (b := 12) (by norm_num)
  push_cast at hc1 hc2
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [thirdI, Vd]
  · have hL := logI_sound hT hl2 hd one_pos
    rw [Nat.cast_one, div_one] at hL
    have hfac : (((((d * d) * (d * d) : ℕ) : ℤ)) : ℝ) = (d : ℝ) ^ 4 := by push_cast; ring
    have hd4 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
    simp only [thirdI]
    rw [Int.cast_mul, Int.cast_mul, hfac, Int.cast_sub, Int.cast_sub, Int.cast_sub, Int.cast_sub]
    unfold Vd
    constructor
    · have hX : ((logI tab l2 d 1).1 : ℝ) - (lDec.2 : ℝ) - ((cdiv (25 * 2 ^ PI) 12 : ℤ) : ℝ) ≤
          2 ^ PI * (Real.log d - Real.log DEC - 25 / 12) := by
        have := hL.1
        have := hDec.2
        linarith
      have := mul_le_mul_of_nonneg_left hX hd4
      linarith
    · have hX : 2 ^ PI * (Real.log d - Real.log DEC - 25 / 12) ≤
          ((logI tab l2 d 1).2 : ℝ) - (lDec.1 : ℝ) - ((fdiv (25 * 2 ^ PI) 12 : ℤ) : ℝ) := by
        have := hL.2
        have := hDec.1
        linarith
      have := mul_le_mul_of_nonneg_left hX hd4
      linarith

theorem iRowStep_le {ri rk : NRec} {ci ck : ℝ} (hi : RecSpecI ri ci) (hk : RecSpecI rk ck) (acc : ℤ × ℤ) :
    ((iRowStep tab l2 lDec ri acc rk).1 : ℝ) ≤ acc.1 + 2 ^ 300 * (ci * ck * Vd (rk.n - ri.n)) := by
  unfold iRowStep
  split_ifs with hsg
  · rw [hk.2.2 hsg]
    simp
  · have h1 := imul_spec (a := (ri.clo, ri.chi)) (b := (rk.clo, rk.chi)) (x := 2 ^ QI * ci) (y := 2 ^ QI * ck)
      ⟨hi.1, hi.2.1⟩ ⟨hk.1, hk.2.1⟩
    have h2 := imul_spec h1 (thirdI_encl hT hl2 hDec (rk.n - ri.n))
    have h300 : (2 : ℝ) ^ 300 = 2 ^ QI * 2 ^ QI * 2 ^ PI := by
      rw [← pow_add, ← pow_add]
      norm_num [QI, PI]
    have hpow : (2 : ℝ) ^ QI * ci * (2 ^ QI * ck) * (2 ^ PI * Vd (rk.n - ri.n)) =
        2 ^ 300 * (ci * ck * Vd (rk.n - ri.n)) := by
      rw [h300]
      ring
    dsimp only
    push_cast
    linarith [h2.1]

/-- `PSum T [i₀, i₁, …] = ∑_{a < b} T i_a i_b`. -/
def PSum (T : ℕ → ℕ → ℝ) : List ℕ → ℝ
  | [] => 0
  | i :: rest => (rest.map (T i)).sum + PSum T rest

theorem iRow_le (rec : ℕ → NRec) (c : ℕ → ℝ) {i : ℕ} (hi : RecSpecI (rec i) (c i)) (rest : List ℕ)
    (hrest : ∀ k ∈ rest, RecSpecI (rec k) (c k)) :
    ((iRow tab l2 lDec (rec i) (rest.map rec)).1 : ℝ) ≤
      2 ^ 300 * (rest.map (fun k => c i * c k * Vd ((rec k).n - (rec i).n))).sum := by
  rw [iRow_eq, List.foldl_map]
  have h := foldl_fst_le (fun acc k => iRowStep tab l2 lDec (rec i) acc (rec k))
    (fun k => 2 ^ 300 * (c i * c k * Vd ((rec k).n - (rec i).n))) (fun k => RecSpecI (rec k) (c k))
    (fun acc k hk => iRowStep_le hT hl2 hDec hi hk acc) rest (0, 0) hrest
  rw [List.sum_map_mul_left] at h
  simpa using h

theorem iBlockAux_le (rec : ℕ → NRec) (c : ℕ → ℝ) :
    ∀ (L : List ℕ) (cnt : ℕ) (acc : ℤ × ℤ), L.length ≤ cnt → (∀ i ∈ L, RecSpecI (rec i) (c i)) →
      ((iBlockAux tab l2 lDec cnt (L.map rec) acc).1 : ℝ) ≤
        acc.1 + 2 ^ 300 * PSum (fun i k => c i * c k * Vd ((rec k).n - (rec i).n)) L := by
  intro L
  induction L with
  | nil =>
    intro cnt acc _ _
    cases cnt <;> simp [iBlockAux, PSum]
  | cons i rest ih =>
    intro cnt acc hlen hspec
    obtain ⟨cnt', rfl⟩ : ∃ cnt', cnt = cnt' + 1 := ⟨cnt - 1, by simp at hlen; omega⟩
    have hi := hspec i (by simp)
    have hrest : ∀ k ∈ rest, RecSpecI (rec k) (c k) := fun k hk => hspec k (List.mem_cons_of_mem i hk)
    rw [List.map_cons]
    simp only [iBlockAux]
    have hlen' : rest.length ≤ cnt' := by simp at hlen; omega
    set t : ℤ × ℤ := if (rec i).sg = 0 then ((0 : ℤ), (0 : ℤ)) else iRow tab l2 lDec (rec i) (rest.map rec)
      with ht
    have h1 := ih cnt' (acc.1 + t.1, acc.2 + t.2) hlen' hrest
    have h2 : (t.1 : ℝ) ≤ 2 ^ 300 * (rest.map (fun k => c i * c k * Vd ((rec k).n - (rec i).n))).sum := by
      rw [ht]
      split_ifs with hsg
      · have hc : c i = 0 := hi.2.2 hsg
        simp [hc]
      · exact iRow_le hT hl2 hDec rec c hi rest hrest
    simp only [PSum]
    push_cast at h1
    linarith

end encl

/-! ## From the blocks to `IR` -/

theorem sum_range_eq_list (n : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

/-- For a symmetric `a` with zero diagonal, `∑_{i ∈ L} ∑_{k ∈ L} a i k = 2 ∑_{i before k} a i k`. -/
theorem square_sum_eq (a : ℕ → ℕ → ℝ) (hsymm : ∀ i k, a i k = a k i) (hdiag : ∀ i, a i i = 0) :
    ∀ L : List ℕ, (L.map (fun i => (L.map (fun k => a i k)).sum)).sum = 2 * PSum a L := by
  intro L
  induction L with
  | nil => simp [PSum]
  | cons x r ih =>
    have h1 : (r.map (fun i => ((x :: r).map (fun k => a i k)).sum)).sum =
        (r.map (fun k => a x k)).sum + (r.map (fun i => (r.map (fun k => a i k)).sum)).sum := by
      have h2 : (fun i => ((x :: r).map (fun k => a i k)).sum) =
          fun i => a x i + (r.map (fun k => a i k)).sum := by
        funext i
        rw [List.map_cons, List.sum_cons, hsymm i x]
      rw [h2, List.sum_map_add]
    have h3 : ((x :: r).map (fun i => ((x :: r).map (fun k => a i k)).sum)).sum =
        ((x :: r).map (fun k => a x k)).sum + (r.map (fun i => ((x :: r).map (fun k => a i k)).sum)).sum := by
      rw [List.map_cons, List.sum_cons]
    rw [h3, h1, ih, List.map_cons, List.sum_cons, hdiag x]
    simp only [PSum]
    ring

theorem PSum_congr (T U : ℕ → ℕ → ℝ) :
    ∀ L : List ℕ, L.Pairwise (fun i k => T i k = U i k) → PSum T L = PSum U L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons x r ih =>
    intro h
    rw [List.pairwise_cons] at h
    simp only [PSum]
    rw [ih h.2, List.map_congr_left (fun k hk => h.1 k hk)]

theorem PSum_const_mul (c : ℝ) (a : ℕ → ℕ → ℝ) :
    ∀ L : List ℕ, PSum (fun i k => c * a i k) L = c * PSum a L := by
  intro L
  induction L with
  | nil => simp [PSum]
  | cons x r ih =>
    simp only [PSum, ih, List.sum_map_mul_left]
    ring

theorem nodes_lt {i k : ℕ} (hik : i < k) (hk : k ≤ NN) : nodes.getD i 0 < nodes.getD k 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge i k with h | h
    · exact (ih h (by omega)).trans (nodes_inc k (by omega))
    · obtain rfl : i = k := by omega
      exact nodes_inc i (by omega)

theorem Lk_div_DEC {d : ℕ} (hd : 0 < d) : 24 * (DEC : ℝ) ^ 4 * Lk ((d : ℝ) / DEC) = Vd d := by
  have hDEC : (0 : ℝ) < DEC := by norm_num [DEC]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold Lk Vd
  rw [abs_of_pos (div_pos hdR hDEC), Real.log_div hdR.ne' hDEC.ne']
  field_simp
  ring

theorem eR_sub_eq {i k : ℕ} (hik : i < k) (hk : k ≤ NN) :
    eR k - eR i = ((nodes.getD k 0 - nodes.getD i 0 : ℕ) : ℝ) / DEC := by
  have h := nodes_lt hik hk
  unfold eR
  rw [Nat.cast_sub h.le, sub_div]
  norm_num [DEC]

theorem term_eq {i k : ℕ} (hik : i < k) (hk : k ≤ NN) :
    CR i * CR k * Vd ((recOfQ QI k).n - (recOfQ QI i).n) =
      24 * (DEC : ℝ) ^ 4 * (CR i * CR k * Lk (eR i - eR k)) := by
  rw [recOfQ_n, recOfQ_n]
  have hd : 0 < nodes.getD k 0 - nodes.getD i 0 := Nat.sub_pos_of_lt (nodes_lt hik hk)
  rw [show eR i - eR k = -(eR k - eR i) by ring, Lk_neg, eR_sub_eq hik hk, ← Lk_div_DEC hd]
  ring

theorem IR_eq_PSum : IR = 2 * PSum (fun i k => CR i * CR k * Lk (eR i - eR k)) (List.range (NN + 1)) := by
  have h1 : IR = ((List.range (NN + 1)).map
      (fun i => ((List.range (NN + 1)).map (fun k => CR i * CR k * Lk (eR i - eR k))).sum)).sum := by
    unfold IR
    rw [sum_range_eq_list]
    exact congrArg List.sum (List.map_congr_left (fun i _ => sum_range_eq_list _ _))
  rw [h1]
  apply square_sum_eq
  · intro i k
    rw [show eR i - eR k = -(eR k - eR i) by ring, Lk_neg]
    ring
  · intro i
    simp [Lk]

theorem PSum_V_eq :
    PSum (fun i k => CR i * CR k * Vd ((recOfQ QI k).n - (recOfQ QI i).n)) (List.range (NN + 1)) =
      12 * (DEC : ℝ) ^ 4 * IR := by
  rw [PSum_congr _ (fun i k => 24 * (DEC : ℝ) ^ 4 * (CR i * CR k * Lk (eR i - eR k))) (List.range (NN + 1))]
  · rw [PSum_const_mul, IR_eq_PSum]
    ring
  · apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range
    intro i k _ hk hik
    exact term_eq hik (Nat.lt_succ_iff.mp (List.mem_range.mp hk))

theorem iBlock_eq_aux (i0 cnt : ℕ) :
    iBlock i0 cnt = iBlockAux TABI L2I (logI TABI L2I DEC 1) cnt (recsI.drop i0) (0, 0) := rfl

/-- **Soundness of the energy check.** The decided inequality `energy_ok` gives `IR ≥ iLoNum / 2^128`. -/
theorem energy_sound (h : (iLoNum : ℤ) * 12 * 10 ^ 40 * 2 ^ 300 ≤ (iBlock 0 5473).1 * 2 ^ 128) :
    (iLoNum : ℝ) / 2 ^ 128 ≤ IR := by
  have hDec := logI_sound tabI_ok l2I_ok (a := DEC) (b := 1) (by norm_num [DEC]) one_pos
  rw [Nat.cast_one, div_one] at hDec
  have hspec : ∀ i ∈ List.range (NN + 1), RecSpecI (recOfQ QI i) (CR i) := by
    intro i hi
    exact recOfQ_spec QI (Nat.lt_succ_iff.mp (List.mem_range.mp hi))
  have hlen : (List.range (NN + 1)).length ≤ 5473 := by
    rw [List.length_range]
    decide
  have hblk := iBlockAux_le tabI_ok l2I_ok hDec (recOfQ QI) CR (List.range (NN + 1)) 5473 (0, 0) hlen hspec
  have hI : iBlockAux TABI L2I (logI TABI L2I DEC 1) 5473 ((List.range (NN + 1)).map (recOfQ QI)) (0, 0) =
      iBlock 0 5473 := by
    rw [iBlock_eq_aux, List.drop_zero, recsI_eq]
  rw [hI, PSum_V_eq] at hblk
  have hcast : ((iLoNum : ℤ) : ℝ) * 12 * 10 ^ 40 * 2 ^ 300 ≤ (((iBlock 0 5473).1 : ℤ) : ℝ) * 2 ^ 128 := by
    exact_mod_cast h
  generalize (iBlock 0 5473).1 = B at hcast hblk
  dsimp only at hblk
  rw [Int.cast_zero, zero_add] at hblk
  rw [Int.cast_natCast] at hcast
  have hDEC4 : (DEC : ℝ) ^ 4 = 10 ^ 40 := by norm_num [DEC]
  rw [hDEC4] at hblk
  have hB : (B : ℝ) * 2 ^ 128 ≤ 2 ^ 300 * (12 * 10 ^ 40 * IR) * 2 ^ 128 :=
    mul_le_mul_of_nonneg_right hblk (by positivity)
  have hK : (0 : ℝ) < 12 * 10 ^ 40 * 2 ^ 300 := by positivity
  have h3 : (iLoNum : ℝ) * (12 * 10 ^ 40 * 2 ^ 300) ≤ (IR * 2 ^ 128) * (12 * 10 ^ 40 * 2 ^ 300) := by
    calc (iLoNum : ℝ) * (12 * 10 ^ 40 * 2 ^ 300) = (iLoNum : ℝ) * 12 * 10 ^ 40 * 2 ^ 300 := by ring
      _ ≤ (B : ℝ) * 2 ^ 128 := hcast
      _ ≤ 2 ^ 300 * (12 * 10 ^ 40 * IR) * 2 ^ 128 := hB
      _ = (IR * 2 ^ 128) * (12 * 10 ^ 40 * 2 ^ 300) := by ring
  rw [div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right h3 hK

end TPMahler.Cert
