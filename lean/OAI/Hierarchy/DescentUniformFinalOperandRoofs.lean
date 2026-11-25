import OAI.Hierarchy.DescentUniformOperandRooms
import OAI.Hierarchy.DescentUniformMetadataRoom

namespace OAI
/-! A common address exponent for the ordinary metadata and seven final operand fields. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open Chronology DescentDatedAddressBook Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

theorem uniform_final_roofs :
    ∃C : ℕ, ∀τ B : ℕ, 0<B → SignedStage.unitRate G t f g reset<B → τ≤B →
      ∀ᶠ h : ℕ in atTop, ∀x : ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h,
        x.model.metadata.ordinaryEnd 0+x.model.operandBook.endAddress 0 ≤ 2^(C*h) := by
  let I := OperandSample G board op t f g reset drift degreeMax
  have R := OperandSample.rooms G board op t f g reset drift degreeMax
  obtain ⟨C,paid⟩ := final_roofs_from_rooms G board op t f g reset drift degreeMax
    (ι := I) (fun _ y => y.tailRate) (fun _ y => y.budget) (fun _ y => y.point) R
  refine ⟨C,fun τ B den _ _ => ?_⟩
  filter_upwards [paid,operand_sample_limits G board op t f g reset τ drift degreeMax B den] with h extent verified
  exact fun x => extent (⟨τ,B,x,verified x⟩ : I h)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
