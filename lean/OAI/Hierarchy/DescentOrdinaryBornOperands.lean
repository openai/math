import OAI.Hierarchy.DescentOrdinaryBornInventory
import OAI.Hierarchy.DescentOperandPhysicalInput
import OAI.Hierarchy.DescentPackedLayoutChoice
import OAI.Hierarchy.DescentBundleSelected
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentOrdinaryAtomFieldRAM

namespace OAI
/-! # The actual public p-word ports of one of the six newborn party rows -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentKernelHistory DescentSixParty GadgetNetwork DescentOperandPhysicalInput
open DescentSIMDLookup DescentOperandStateBanks DescentBundleHistory
open scoped Classical Fin.CommRing
noncomputable section

variable {F P I : Type} [Field F] [Fintype I] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (profiles : I→Profile G.C) (grain : ℕ)

theorem actual_units (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (i : I) (j : Fin 6) (r : RolePort j) :
    units (actual G grain) (z i) (DescentPacking.PackedMatch.LayoutSum.profileCode G.C (profiles i)).val (role r)=
      boundaryWidth (physical W.graph pick (branchWidth G z profiles)) (.inr (i,j))
        (nativeRole W.graph pick (branchWidth G z profiles) i j r)/grain:=by
  rcases r with (s|s)|(s|s)
  · change z i*G.b/grain=W.graph.width (pick (i,s.val))/grain
    rw [fit]
  · change z i*G.b/grain=W.graph.width (pick (i,s.val))/grain
    rw [fit]
  · change z i*((profileDigits G.C _ s.val).val+G.k)/grain=z i*(((profiles i).val s.val).val+G.k)/grain
    rw [profile_read]
  · change z i*((profileDigits G.C _ s.val).val+G.k)/grain=z i*(((profiles i).val s.val).val+G.k)/grain
    rw [profile_read]

end
end Hierarchy.DescentOrdinaryBorn

end OAI
