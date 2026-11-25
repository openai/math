import OAI.Hierarchy.DescentSeedInitialArgumentCapacity
import OAI.Hierarchy.DescentNamedResetOutput

namespace OAI
/-! # The original three input blocks fit the retained argument capacity -/
namespace Hierarchy.DescentSixParty.AtomSchedule
open DescentCompiler DescentDatedAddressBook
noncomputable section
variable {F : Type} [Field F] (S : DescentCompiler.AtomSchedule) (G : PoweredGadget F)

theorem prior_capacity (age p drift M P b : ℕ) (v : StageVenueTail.Date)
    (late : 0<S.height) (base : G.b≤2^S.capGain) :
    let prior:=ResetOutput.Prior.atDate G S age p drift M P b v
    prior.nodes≤S.retainedNodes ∧ prior.arguments≤S.retainedArgumentsAt G drift :=by
  by_cases z:age=0
  · refine ⟨?_, ?_⟩
    · simp [ResetOutput.Prior.atDate,z,retainedNodes,DescentCompiler.AtomSchedule.epochPower]
      exact Nat.succ_le_of_lt (by positivity)
    · simpa [ResetOutput.Prior.atDate,z] using S.seed_argument_capacity G p drift late base
  · simp [ResetOutput.Prior.atDate,z]

end
end Hierarchy.DescentSixParty.AtomSchedule

end OAI
