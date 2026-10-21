import TPMahler.CheckSound5

/-!
# Soundness of the checker, part 6: chord leaves

`chordLB_sound`: if `chordLB (mkCtx iLoNum 128) Xp Xq k x0q mask = some (lp, lq)` and `I ≥ iLoNum/2^128`, then
`F(x) ≥ min(lp, lq) / 2^P` on `[Xp/D, Xq/D]`.
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

/-- Chord bound for `A`, tangent for the convex `TP`, and `TS ≥ 0`. -/
theorem chord_tangent_combine {p q : ℝ} (hpq : p < q) {A TP TS A' A'' : ℝ → ℝ} {M d x0 : ℝ}
    (hA : ContinuousOn A (Icc p q)) (hA' : ∀ x ∈ Ioo p q, HasDerivAt A (A' x) x)
    (hA'' : ∀ x ∈ Ioo p q, HasDerivAt A' (A'' x) x) (hM : ∀ x ∈ Ioo p q, A'' x ≤ M)
    (hTP : ConvexOn ℝ (Icc p q) TP) (hx0 : x0 = p ∨ x0 = q) (hd : HasDerivAt TP d x0)
    (hTS : ∀ x ∈ Icc p q, 0 ≤ TS x) :
    ∀ x ∈ Icc p q, min (A p + TP x0 + d * (p - x0)) (A q + TP x0 + d * (q - x0)) - max M 0 * (q - p) ^ 2 / 8
      ≤ A x + TP x + TS x := by
  intro x hx
  have hc := chord_lower hpq hA hA' hA'' hM x hx
  have ht := tangent_lower_end hpq.le hTP hx0 hd x hx
  have hs := hTS x hx
  have hqp : 0 < q - p := by linarith
  set lp := A p + TP x0 + d * (p - x0)
  set lq := A q + TP x0 + d * (q - x0)
  have hcomb : ((q - x) * A p + (x - p) * A q) / (q - p) + (TP x0 + d * (x - x0)) =
      ((q - x) * lp + (x - p) * lq) / (q - p) := by
    simp only [lp, lq]
    field_simp
    ring
  have hmin : min lp lq ≤ ((q - x) * lp + (x - p) * lq) / (q - p) := by
    rw [le_div_iff₀ hqp]
    have h1 : 0 ≤ q - x := by linarith [hx.2]
    have h2 : 0 ≤ x - p := by linarith [hx.1]
    have := min_le_left lp lq
    have := min_le_right lp lq
    nlinarith
  linarith

/-- The per-polynomial results of a successful fold. -/
theorem polyRes_facts {Xp Xq D : ℕ} {LD : ℤ × ℤ} {x0q : Bool} {mask : ℕ} {T : ℤ × ℤ × ℤ × ℤ × ℤ}
    (h : (List.zip polys (List.zip cwNum cwSh)).zipIdx.foldl
      (polyFold (fun x => polyLeaf TAB L2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2))
      (some (0, 0, 0, 0, 0)) = some T) :
    ∃ v : ℕ → ℤ × ℤ × ℤ × ℤ × ℤ,
      (∀ j < 19, polyLeaf TAB L2 Xp Xq D LD x0q (Nat.testBit mask j) (polys.getD j []) (cwNum.getD j 0)
        (cwSh.getD j 0) = some (v j)) ∧
      T = ∑ j ∈ Finset.range 19, v j := by
  set g := fun x : (List Int × ℕ × ℕ) × ℕ =>
    polyLeaf TAB L2 Xp Xq D LD x0q (Nat.testBit mask x.2) x.1.1 x.1.2.1 x.1.2.2 with hg
  obtain ⟨hsome, hT⟩ := polyFold_some g _ _ _ h
  rw [polyList_eq] at hsome hT
  set elt := fun j : ℕ => ((polys.getD j [], (cwNum.getD j 0, cwSh.getD j 0)), j) with helt
  refine ⟨fun j => (g (elt j)).getD 0, ?_, ?_⟩
  · intro j hj
    have hmem : elt j ∈ (List.range 19).map elt := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have := hsome (elt j) hmem
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp this
    show g (elt j) = some ((g (elt j)).getD 0)
    rw [hv]; rfl
  · rw [hT, show ((0, 0, 0, 0, 0) : ℤ × ℤ × ℤ × ℤ × ℤ) = 0 from rfl, zero_add, List.map_map]
    exact list_sum_range (fun j => (g (elt j)).getD 0) 19

end TPMahler.Cert
