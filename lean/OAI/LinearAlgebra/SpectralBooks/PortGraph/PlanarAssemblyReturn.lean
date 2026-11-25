import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarReturnEmbedding
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyIncidence
import OAI.Geometry.HyperbolicGroups.IndexedFace

/-! # Reading each patch's stub order in the glued map -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.StubPairing

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch PlanarSurgery

universe u
variable {J : Type u} {S : J → Type u} (P : ∀ i, OpenPiece (S i)) [∀ i, Fintype (S i)]

/-- Local rotations and the selected spanning tree. The final two conditions
say that the selected bands merge the incident vertex disks into one disk. -/
structure PieceDiskData where
  turn : ∀ i, Perm (PieceDart P i)
  forest : ∀ i, Perm (PieceDart P i)
  subpair : ∀ i x, forest i x = x ∨ forest i x = insideMate P i x
  oneBoundary : ∀ i x y, (turn i * forest i).SameCycle x y
  cost : ∀ i, 2 * (cycles (turn i) - cycles (turn i * forest i)) = ((forest i).support.card : ℤ)

variable (C : StubPairing S) [Fintype J]

omit [Fintype J] in
theorem localCover (A : PieceDiskData P) (live : ∀ i, Nonempty (S i)) (i : J) :
    Covers (A.turn i * A.forest i) (Function.Embedding.inr : S i ↪ PieceDart P i) :=
  fun x => ⟨(live i).some, A.oneBoundary i x _⟩

/-- Return at a named stub inside its record or its replacement tree. -/
def PieceDiskData.stubTurn (A : PieceDiskData P) (live : ∀ i, Nonempty (S i)) (i : J) : Perm (S i) :=
  onStubs _ _ (localCover P A live i)

variable (num : (C.assemble P).Numbering) (A : PieceDiskData P)
  (hturn : ∀ x, C.dartEquiv P (num.turn x) = Equiv.sigmaCongrRight A.turn (C.dartEquiv P x))
  (live : ∀ i, Nonempty (S i))

private def pieceIn (i : J) (x : PieceDart P i) := (C.dartEquiv P).symm ⟨i,x⟩

include hturn in
private theorem pieceIn_turn (i : J) (x : PieceDart P i) :
    pieceIn P C i ((A.turn i * A.forest i) x) = C.turnAfterForest P num A.forest (pieceIn P C i x) := by
  apply (C.dartEquiv P).injective
  rw [C.dartEquiv_turnAfterForest P num A.turn A.forest hturn]
  simp only [pieceIn, Equiv.apply_symm_apply]
  rfl

omit [∀ i, Fintype (S i)] [Fintype J] in
private theorem pieceIn_mark (i : J) (s : S i) :
    pieceIn P C i (.inr s) = C.stubMark P ⟨i,s⟩ := by
  apply (C.dartEquiv P).injective
  rw [C.dartEquiv_stubMark]
  exact (C.dartEquiv P).apply_symm_apply _

omit [∀ i, Fintype (S i)] [Fintype J] in
private theorem pieceIn_reflect (i : J) (x : PieceDart P i)
    (h : pieceIn P C i x ∈ Set.range (C.stubMark P)) :
    x ∈ Set.range (Function.Embedding.inr : S i ↪ PieceDart P i) := by
  obtain ⟨⟨k,t⟩,h⟩ := h
  have hh := congrArg (C.dartEquiv P) h
  rw [C.dartEquiv_stubMark] at hh
  change (⟨k,.inr t⟩ : Σ i, PieceDart P i) = C.dartEquiv P ((C.dartEquiv P).symm ⟨i,x⟩) at hh
  rw [Equiv.apply_symm_apply] at hh
  cases hh
  exact ⟨_,rfl⟩

include hturn live in
theorem assembledCover : Covers (C.turnAfterForest P num A.forest) (C.stubMark P) := by
  intro x
  obtain ⟨⟨i,z⟩,rfl⟩ := (C.dartEquiv P).symm.surjective x
  let s := (live i).some
  refine ⟨⟨i,s⟩, ?_⟩
  rw [← pieceIn_mark]
  exact semiconj_perm_sameCycle (pieceIn_turn P C num A hturn i) (A.oneBoundary i z (.inr s))

include hturn in
theorem assembled_onStubs :
    onStubs _ _ (assembledCover P C num A hturn live) = Equiv.sigmaCongrRight (A.stubTurn P live) := by
  apply Equiv.ext
  rintro ⟨i,s⟩
  exact onStubs_map _ _ _ _ (localCover P A live i) (assembledCover P C num A hturn live)
    (pieceIn P C i) (Sigma.mk i) (pieceIn_turn P C num A hturn i)
    (pieceIn_mark P C i) (pieceIn_reflect P C i) s

include hturn in
/-- Once interpatch edges are restored, the entire face count is computed on
the common set of stubs, by alternating their pairing with the local rotations. -/
theorem closedFaceCount :
    cycles (C.turnAfterForest P num A.forest * C.outsidePairing P) =
      cycles (Equiv.sigmaCongrRight (A.stubTurn P live) * C.stubMate) := by
  let p := C.turnAfterForest P num A.forest
  have hc := assembledCover P C num A hturn live
  rw [← assembled_onStubs P C num A hturn live]
  apply cycles_close p (C.stubMark P) hc C.stubMate (p * C.outsidePairing P)
  · intro s
    apply congrArg p
    change C.outsidePairing P (C.exteriorMark P (C.ends.symm s)) =
      C.exteriorMark P (C.ends.symm (C.stubMate s))
    rw [C.outsidePairing_mark]
    simp [stubMate]
  · intro x hx
    change p (C.outsidePairing P x) = p x
    apply congrArg p
    apply C.outsidePairing_off_mark
    rintro ⟨q,rfl⟩
    exact hx ⟨C.ends q, by simp [stubMark]⟩

end PortGraph.StubPairing

end

end SpectralBooks
end LinearAlgebra
end OAI
