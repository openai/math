import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyForest
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyReturn
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortEuler

/-! # Sphericity of a single replacement disk

There are no exterior wires when the assembly has just one occurrence. Its
tree contour is both the contracted vertex and its only face if any darts
exist. With no darts all terms of the picture Euler equation vanish.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.StubPairing

universe u
variable {J : Type u} {S : J → Type u} [Fintype J] [∀ i, Fintype (S i)]

theorem singleOccurrence_spherical [Subsingleton J] (C : StubPairing S) (P : ∀ i, OpenPiece (S i))
    (num : (C.assemble P).Numbering) (A : PieceDiskData P)
    (ht : ∀ x, C.dartEquiv P (num.turn x) = Equiv.sigmaCongrRight A.turn (C.dartEquiv P x))
    (r : Vertex P) (hc : (C.assemble P).ConnectedFrom r) (full : A.forest = insideMate P) :
    num.rotation.picture.GenusZero := by
  cases isEmpty_or_nonempty (C.Edge P) with
  | inl h => simp [PictureMap.GenusZero, PictureMap.euler, cycles_eq_card_classes]
  | inr h =>
    have hout : C.outsidePairing P = 1 := by
      apply Equiv.ext
      intro x
      exact (C.outsidePairing_apply P x).trans (ite_eq_left (Subsingleton.elim _ _))
    have orbits := C.assembly_forest_orbit P num A.turn A.forest ht A.oneBoundary
    rw [full] at orbits
    let p := num.turn * C.liftPiecePerm P (insideMate P)
    have horbit (x y : C.Edge P × Bool) : p.SameCycle x y := (orbits x y).mpr (Subsingleton.elim _ _)
    have hcycles : cycles p = 1 := by
      simpa only [Fintype.card_unit, Nat.cast_one] using cycles_of_classifier p (fun _ => ())
        (fun x y => ⟨fun _ => rfl, fun _ => horbit x y⟩) (fun _ => ⟨(h.some,false),rfl⟩)
    have hcomponent := num.rotation.picture_component_card (PlanarPatch.underlying_connected_of_connectedFrom _ _ hc)
    apply (C.assembly_inside_euler_iff P num A.turn ht (full ▸ A.cost)).mp
    change cycles p + cycles (p * C.outsidePairing P) - _ = _
    rw [hout, mul_one, hcycles, hcomponent]
    simp

end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
