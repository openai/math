import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContourWord
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementSmallShape
import OAI.LinearAlgebra.SpectralBooks.PortGraph.ReplacementEncoder
import OAI.LinearAlgebra.SpectralBooks.TrivalentNumberedTurn
import OAI.Geometry.HyperbolicGroups.WordPictureBase

/-! # Boundary of the one-role replacement

Every dart of a direct term is an old named stub. Its vertex ports are numbered
in contour order, so one turn already reaches the next stub in the old word.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape
open ReplacementTemplate PlanarSurgery

variable {K : ℕ} (R : PatchShape K)

/-- The direct term turns through the named stubs in their old contour order. -/
def singleTurn : Perm ((Empty × Bool) ⊕ R.Stub) :=
  Equiv.sumCongr (.refl _) R.contourStubWord.formPerm

/-- Cross all internal wires in the one-role term. -/
def singleMate : Perm ((Empty × Bool) ⊕ R.Stub) :=
  Equiv.sumCongr PortGraph.cross (.refl _)

@[simp] theorem singleMate_eq_one : R.singleMate = 1 := by
  apply Equiv.ext
  rintro (⟨e,_⟩ | s)
  · exact e.elim
  · rfl

private theorem contourStubWord_successor (hc : R.InternallyConnected)
    (i : Fin (Fintype.card R.Stub)) :
    R.contourStubWord.formPerm (R.contourStubEquiv hc i) =
      R.contourStubEquiv hc (finRotate _ i) := by
  rw [R.contourStubWord_eq_ofFn hc, List.ofFn_eq_map,
    formPerm_map_apply _ (R.contourStubEquiv hc).injective,
    ← (finRange_boundary _).turn i (List.mem_finRange i)]

/-- The single role's actual local port numbering gives the stated boundary turn. -/
theorem singleTurn_numbered (hc : R.InternallyConnected) :
    ((singleRole (fun s : R.Stub => s.val.side)).piece).slotTurn
      (singleNumbering _ (R.contourStubEquiv hc).symm) = R.singleTurn := by
  let O := (singleRole (fun s : R.Stub => s.val.side)).piece
  let num : (v : O.Vertex) → O.Ports v ≃ Fin (Fintype.card R.Stub) :=
    singleNumbering (fun s : R.Stub => s.val.side) (R.contourStubEquiv hc).symm
  apply Equiv.ext
  intro d
  obtain ⟨⟨v,p⟩,rfl⟩ := O.localDarts.surjective d
  obtain ⟨i,rfl⟩ := (num v).symm.surjective p
  change O.slotTurn num (O.localDarts ⟨v,(num v).symm i⟩) = _
  rw [OpenPiece.slotTurn_port, Equiv.apply_symm_apply]
  exact congrArg Sum.inr (R.contourStubWord_successor hc i).symm

/-- The contour has one orbit whenever there are any darts. -/
theorem singleContour_sameCycle (hc : R.InternallyConnected) (x y : (Empty × Bool) ⊕ R.Stub) :
    (R.singleTurn * R.singleMate).SameCycle x y := by
  rw [singleMate_eq_one, mul_one]
  rcases x with ⟨e,_⟩ | x
  · exact e.elim
  rcases y with ⟨e,_⟩ | y
  · exact e.elim
  have hb : IsBoundary R.contourStubWord.formPerm R.contourStubWord :=
    ⟨R.contourStubWord_nodup, fun _ _ => rfl⟩
  exact semiconj_perm_sameCycle (j := Sum.inr) (fun _ => rfl)
    (hb.sameCycle (R.mem_contourStubWord hc x) (R.mem_contourStubWord hc y))

/-- The empty forest removes no vertex cycles and has no moved darts. -/
theorem singleContour_cost :
    2 * (cycles R.singleTurn - cycles (R.singleTurn * R.singleMate)) =
      (R.singleMate.support.card : ℤ) := by simp

/-- Every stub is marked, so this cover also handles the dartless direct term. -/
theorem singleContour_covers :
    Covers (R.singleTurn * R.singleMate) (.inr : R.Stub ↪ (Empty × Bool) ⊕ R.Stub) := by
  rintro (⟨e,_⟩ | s)
  · exact e.elim
  · exact ⟨s, .rfl⟩

/-- The first positive return word at a direct term agrees with the record. -/
theorem singleContour_onStubs
    (cover : Covers (R.singleTurn * R.singleMate) (.inr : R.Stub ↪ (Empty × Bool) ⊕ R.Stub)) :
    onStubs _ _ cover = R.contourStubWord.formPerm := by
  apply Equiv.ext
  intro s
  exact firstStub_mark _ _ cover (R.contourStubWord.formPerm s)

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
