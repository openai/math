import OAI.Hierarchy.DescentOriginalSeedArchive
import OAI.Hierarchy.DescentPrimitiveAtNode

namespace OAI
/-! # The primitive dictionary attached to the original seed census -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty
noncomputable section
variable {F : Type} [Field F] {n h s Z p : ℕ} {G : PoweredGadget F} (op : RotorSpec) (menu : Runnable F op)
open Catalyst DescentInitialHost in
def seeded (X : Approximation F n h) {cp : ℕ} (c : (initialGroup X cp s).Choice) :
    Encoding (Label G s Z op) (dictionary G op menu p) (Chronology.seedArchive X cp s c).bit :=
  ⟨Sum.inl,fun _=>rfl⟩

end
end Hierarchy.DescentPrimitivePalette

end OAI
