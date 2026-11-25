import OAI.Hierarchy.DescentOriginalRetainedWorld
import OAI.Hierarchy.DescentBundleSeed

namespace OAI
/-! # Genuine recipe fields and the physical stride of the original seed -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentSixParty DescentInitialHost Catalyst
noncomputable section
variable {F : Type} [Field F] {k n p R : ℕ} (X : Approximation F k n) (count s : ℕ)
variable (hp : 0<p) (one : 1≤R) (multiple : p∣s)

def seedRetained (c : (initialGroup X count s).Choice) : Retained p R ((initialGroup X count s).state c) where
  description := BitDescription.initial X count s c
  shape := {
    sites:=fun v=>initialShape X count s c v hp multiple
    stride:=fun _ _ _ _=>one
    edges:=fun e=> by
      let N:=((initialGroup X count s).state c).graph
      have edgeWidth : N.width e = s :=
        initial_width X count s c (N.src e) (.inl ⟨e,Or.inl rfl⟩)
      exact (congrArg (fun width : ℕ => p ∣ width) edgeWidth).mpr multiple }


end
end Hierarchy.DescentBundleHistory

end OAI
