import OAI.Computability.BorderVNP.PackedBankInheritedDenseEpochs

/-! # Fixed record multipliers for an actual installed site epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Packing InheritedBank
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- One uniform factor for a complete outer epoch of genuinely stored public site programs. -/
noncomputable def SiteSchedule.publicProgramFactor := 1040*S.bankRecordFactor

/-- A partial sequence of inner stages and its initial subdivision fit the full
epoch factor, before the terminal route is applied. -/
theorem SiteSchedule.partialProgramFactor_le (n : ℕ) (hn : n≤S.rounds) (B : ℕ) :
    (1+∑ i, loadMultiplier e*(S.source.pattern i).record*S.fanIn)^n*
      (1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*B) ≤
      S.publicProgramFactor*B := by
  let f := 1+∑ i, loadMultiplier e*(S.source.pattern i).record*S.fanIn
  let subdiv := 1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius))
  let b := 1040*subdiv*B
  have hf : 0 < f := Nat.add_pos_left (by decide : 0 < 1) _
  apply (Nat.mul_le_mul_right b (Nat.pow_le_pow_right hf hn)).trans
  apply (Nat.le_mul_of_pos_left (f^S.rounds*b) (show 0 < 1+S.finalCap by omega)).trans_eq
  change (1+S.finalCap)*(f^S.rounds*(1040*subdiv*B)) = 1040*((1+S.finalCap)*f^S.rounds*subdiv)*B
  ring

end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
