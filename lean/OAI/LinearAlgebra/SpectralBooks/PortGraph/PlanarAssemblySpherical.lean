import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyReturn
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyForest
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarSingleOccurrence
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarFaceTotals
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarNamingCertificates

/-! # Sphericity of a replacement glued along the same external wires

On the common stub set the vertex count is the number of occurrences, every
external wire contributes one edge, and the face permutation crosses a wire
then takes the next stub on the local tree boundary. Equality of those cyclic
orders identifies the Euler count of the two assembled numbered maps.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.StubPairing

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch PlanarSurgery

universe u
variable {J : Type u} {S : J → Type u} [Fintype J] [∀ i, Fintype (S i)]
    (C : StubPairing S) (P Q : ∀ i, OpenPiece (S i))
    (n : (C.assemble P).Numbering) (m : (C.assemble Q).Numbering)
    (A : PieceDiskData P) (B : PieceDiskData Q)
    (ht : ∀ x, C.dartEquiv P (n.turn x) = Equiv.sigmaCongrRight A.turn (C.dartEquiv P x))
    (hu : ∀ x, C.dartEquiv Q (m.turn x) = Equiv.sigmaCongrRight B.turn (C.dartEquiv Q x))

omit [∀ i, Fintype (S i)] in
/-- The component of every nonempty connected numbered assembly is intrinsic
to the incidence graph. -/
private theorem one_component [Nonempty C.Wire] (r : Vertex P) (h : (C.assemble P).ConnectedFrom r) :
    Nat.card (Quotient n.rotation.picture.components) = 1 := by
  let : Nonempty (C.Edge P) := ⟨Sum.inl (Classical.arbitrary C.Wire)⟩
  exact n.rotation.picture_component_card (PlanarPatch.underlying_connected_of_connectedFrom _ r h)

include ht hu in
theorem spherical_replacement_of_live (live : ∀ i, Nonempty (S i)) (r : Vertex P) (s : Vertex Q)
    (hr : (C.assemble P).ConnectedFrom r) (hs : (C.assemble Q).ConnectedFrom s)
    (full : B.forest = insideMate Q)
    (matchTurn : ∀ i, A.stubTurn P live i = B.stubTurn Q live i)
    (hG : n.rotation.picture.GenusZero) : m.rotation.picture.GenusZero := by
  let : Nonempty C.Wire := ⟨(C.ends.symm ⟨r.1,(live r.1).some⟩).1⟩
  have old := C.assembly_forest_euler P n A.turn A.forest ht A.oneBoundary A.subpair A.cost hG
  have c₁ := C.assembly_forest_cycles P n A.turn A.forest ht A.oneBoundary live
  have c₂ := C.assembly_forest_cycles Q m B.turn B.forest hu B.oneBoundary live
  have f₁ := closedFaceCount P C n A ht live
  have f₂ := closedFaceCount Q C m B hu live
  have ho := C.one_component P n r hr
  have hn := C.one_component Q m s hs
  have cost := B.cost
  rw [full] at cost
  apply (C.assembly_inside_euler_iff Q m B.turn hu cost).mp
  rw [← full, c₂, C.outsidePairing_support_card, hn]
  rw [c₁, C.outsidePairing_support_card, ho] at old
  change _ + cycles (C.turnAfterForest P n A.forest * C.outsidePairing P) - _ = _ at old
  change _ + cycles (C.turnAfterForest Q m B.forest * C.outsidePairing Q) - _ = _
  rw [f₁, funext matchTurn] at old
  rwa [f₂]

include ht hu in
/-- Replacing every connected patch by a disk tree with the specified cyclic
stub order preserves sphericity of the assembled map, including zero stubs. -/
theorem spherical_replacement (r : Vertex P) (s : Vertex Q)
    (hr : (C.assemble P).ConnectedFrom r) (hs : (C.assemble Q).ConnectedFrom s)
    (represented : ∀ i, Nonempty (P i).Vertex) (full : B.forest = insideMate Q)
    (matchTurn : ∀ (live : ∀ i, Nonempty (S i)) i, A.stubTurn P live i = B.stubTurn Q live i)
    (hG : n.rotation.picture.GenusZero) : m.rotation.picture.GenusZero := by
  cases subsingleton_or_nontrivial J with
  | inl h => exact C.singleOccurrence_spherical Q m B hu s hs full
  | inr h =>
    have live := C.nonempty_stub (C.occurrence_connected P hr represented)
    exact C.spherical_replacement_of_live P Q n m A B ht hu live r s hr hs full (matchTurn live) hG

end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
