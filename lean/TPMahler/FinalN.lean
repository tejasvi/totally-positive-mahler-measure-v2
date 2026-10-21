import TPMahler.CertChecks
import TPMahler.LeavesN
import TPN.Globals
import TPMahler.Assembly

/-!
# Theorem 1.1 of the paper, track N

The computational facts are decided by `native_decide` (shards `TPN.*`: the tiling in 43 blocks, energy, budget and
tails in `TPN.Globals`). The statements are those of `TPMahler.Statement` (`tp_main`, `tp_omega`, `tp_limit_point`,
`exp_m0_gt`); `EnergySmoothing` is the one named hypothesis, and `PwLinClosedForm` (kept in the signatures as in the
statement file) is proved in `TPMahler.ClosedForm`.
-/

open Polynomial Filter Topology
open AuxCommon

namespace TPMahler.Cert

open TPCore AuxCore

theorem certHyp_N : CertHyp Qc cR m0 NN eR GR sR :=
  certHyp_of_checks (of_decide_eq_true TPCore.TPN.energy_ok) TPCore.TPN.budget_ok
    (of_decide_eq_true TPCore.TPN.left_tail_ok) (of_decide_eq_true TPCore.TPN.right_tail_ok) leavesOK_full_N

end TPMahler.Cert

namespace TPMahler.N

/-- **Theorem 1.1** (track N). -/
theorem tp_main (hE : EnergySmoothing) (_hC : PwLinClosedForm) (ε : ℝ) (hε : 0 < ε) :
    (TPLow (m0 - ε)).Finite :=
  Cert.certHyp_N.tp_main hE ε hε

/-- **Theorem 1.1**, second form (track N). -/
theorem tp_omega (hE : EnergySmoothing) (_hC : PwLinClosedForm) :
    {α : ℂ | ∃ P : ℤ[X], IsMinpolyZ P α ∧ AllRootsPos P ∧
      (toC P).mahlerMeasure ^ ((P.natDegree : ℝ)⁻¹) ≤ 17234615 / 10000000}.Finite :=
  Cert.certHyp_N.tp_omega hE

/-- **Theorem 1.1**, third form (track N). -/
theorem tp_limit_point (hE : EnergySmoothing) (_hC : PwLinClosedForm) :
    ∀ y : ℝ, AccPt y (𝓟 Lplus) → Real.exp m0 ≤ y :=
  Cert.certHyp_N.limit_point hE

theorem exp_m0_gt : (17234615 / 10000000 : ℝ) < Real.exp m0 := lt_exp_m0

end TPMahler.N
