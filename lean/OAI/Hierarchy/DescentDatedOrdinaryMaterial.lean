import OAI.Hierarchy.DescentDatedMaterialExtent
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentPrivateInstalledWidth

namespace OAI
/-! The original ordinary date determines both pitches and every donor source-table width. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
theorem material_shift (floor : ℕ) : v.materialEnd floor=floor+v.materialEnd 0 :=by
  rw [materialEnd,v.material.translated,materialStart,PriorHeader.translated,v.donor_shift]
  simp only [materialEnd,materialStart,PriorHeader.translated _ _ _ _ (v.donorEnd 0),Nat.add_assoc]
  rw [v.material.translated (v.donorEnd 0 + _),Nat.add_assoc]

theorem material_spent (floor : ℕ) : v.donorEnd floor≤v.materialEnd floor :=
  (v.signed_stage_paid floor).1


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
