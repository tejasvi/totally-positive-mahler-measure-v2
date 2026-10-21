import TPCore.Leaves

/-! Global checks of the certificate (N): data, budget, energy, tails. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace TPCore.TPN

theorem data_ok : dataOK = true := by native_decide

theorem budget_ok : budgetOK = true := by native_decide

/-- `I ≥ iLoNum / 2^128`: the energy blocks give `I ≥ iBlock.1 / (12 · 10^40 · 2^300)`. -/
theorem energy_ok : decide ((iLoNum : Int) * 12 * 10 ^ 40 * 2 ^ 300 ≤ (iBlock 0 5473).1 * 2 ^ 128) = true := by
  native_decide

theorem left_tail_ok : decide (0 < leftTailLB (mkCtx iLoNum 128) DEC 30) = true := by native_decide

theorem right_tail_ok : decide (0 < rightTailLB (mkCtx iLoNum 128) (XT * DEC)) = true := by native_decide

end TPCore.TPN
