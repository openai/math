import OAI.Hierarchy.DescentProfiledUniformCanvas
import OAI.Hierarchy.DescentProfiledUniformIngress

namespace OAI
/-! The selected reset's input and Canvas share the actual prior tape. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)
local notation "A" h:arg => ResetArea G board op t f g reset drift degreeMax h
set_option quotPrecheck false in
local notation "I" h:arg => {x : A h // x.Verified ∧ x.frozen ≤ Nat.log 2 h}

theorem uniform_entrance : DescentDatedAddressBook.ResetOutput.EntranceRoom
    (fun h (i:I h)=>i.val.stage) (fun _ i=>i.val.inside) ∧
    DescentResetCanvasIngress.Layout.ScalarRoom (fun h (i:I h)=>i.val.stage.ingress) :=
  ⟨uniform_canvas G board op t f g reset drift degreeMax,uniform_ingress G board op t f g reset drift degreeMax⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea

end OAI
