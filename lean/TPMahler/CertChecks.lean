import TPMahler.CheckSound10
import TPMahler.TailSound2
import TPMahler.EnergySound
import TPMahler.CertData

/-!
# The certificate from the computational checks

`certHyp_of_checks`: the five Boolean/integer facts that the checker decides (energy, budget, left tail, right tail,
tiling of `[2^-30, 21]`) give `CertHyp Qc cR m0 NN eR GR sR`. The N track decides them with `native_decide`
(`TPMahler.FinalN`), the K track with `decide +kernel` (`TPMahler.FinalK`).
-/

open Polynomial Set

namespace TPMahler.Cert

open TPCore AuxCore AuxCommon

theorem certHyp_of_checks
    (hE : (iLoNum : ℤ) * 12 * 10 ^ 40 * 2 ^ 300 ≤ (iBlock 0 5473).1 * 2 ^ 128)
    (hB : budgetOK = true)
    (hL : 0 < leftTailLB (mkCtx iLoNum 128) DEC 30)
    (hR : 0 < rightTailLB (mkCtx iLoNum 128) (XT * DEC))
    (hT : leavesOK (mkCtx iLoNum 128) 10000000000 30 leaves 210000000000 0 = true) :
    CertHyp Qc cR m0 NN eR GR sR := by
  have hI := energy_sound hE
  have hbud := budget_sound hB
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hcov := (leavesOK_sound hI leaves 10000000000 30 210000000000 0 (by unfold DEC; norm_num) hT).2
  refine certHyp_of hbud ?_
  intro x hx hQ
  by_cases h1 : x ≤ (DEC : ℝ) / (DEC * 2 ^ 30 : ℕ)
  · have hl := leftTailLB_sound hI hx h1 hQ
    have h0 : (0 : ℝ) < (leftTailLB (mkCtx iLoNum 128) DEC 30 : ℝ) / 2 ^ P :=
      div_pos (by exact_mod_cast hL) hP
    linarith
  · have h1' := (not_le.mp h1).le
    have e1 : ((10000000000 : ℕ) : ℝ) / ((DEC * 2 ^ 30 : ℕ) : ℝ) = (DEC : ℝ) / (DEC * 2 ^ 30 : ℕ) := by
      unfold DEC; norm_num
    by_cases h2 : x < ((210000000000 : ℕ) : ℝ) / ((DEC * 2 ^ 0 : ℕ) : ℝ)
    · exact (hcov x ⟨by rw [e1]; exact h1', h2⟩ hQ).le
    · have h2' := not_lt.mp h2
      have e2 : ((210000000000 : ℕ) : ℝ) / ((DEC * 2 ^ 0 : ℕ) : ℝ) = ((XT * DEC : ℕ) : ℝ) / DEC := by
        unfold XT DEC; norm_num
      rw [e2] at h2'
      have hr := rightTailLB_sound hI hB h2' hQ
      have h0 : (0 : ℝ) < (rightTailLB (mkCtx iLoNum 128) (XT * DEC) : ℝ) / 2 ^ P :=
        div_pos (by exact_mod_cast hR) hP
      linarith

end TPMahler.Cert
