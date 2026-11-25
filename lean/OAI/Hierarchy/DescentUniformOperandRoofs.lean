import OAI.Hierarchy.DescentUniformFinalOperandRoofs

namespace OAI
/-! A single address exponent for the four actual operand allocations across ordinary dates. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentDatedAddressBook Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

theorem uniform_operand_roofs :
    ∃C : ℕ, ∀τ B : ℕ, 0<B → SignedStage.unitRate G t f g reset<B → τ≤B →
      ∀ᶠ h : ℕ in atTop, ∀x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h,
        x.model.vector.endAddress 0+x.model.resolver.endAddress 0+
        x.model.metadata.ordinaryEnd 0+x.model.operandBook.endAddress 0 ≤ 2^(C*h) := by
  let I := OperandSample G board op t f g reset drift degreeMax
  have R := OperandSample.rooms G board op t f g reset drift degreeMax
  have earlier := (DescentOperandVectorArena.Layout.extent_rate _ R.vector).add
    (DescentDatedPriorOperand.Layout.extent_rate _ R.resolver)
  have later := final_roofs_from_rooms G board op t f g reset drift degreeMax
    (ι:=I) (fun _ y=>y.tailRate) (fun _ y=>y.budget) (fun _ y=>y.point) R
  obtain ⟨C,all⟩ := earlier.add later
  refine ⟨C,fun τ B den _ _=>?_⟩
  filter_upwards [all,operand_sample_limits G board op t f g reset τ drift degreeMax B den] with h ready verified
  intro x
  simpa only [Nat.add_assoc] using ready (⟨τ,B,x,verified x⟩ : I h)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
