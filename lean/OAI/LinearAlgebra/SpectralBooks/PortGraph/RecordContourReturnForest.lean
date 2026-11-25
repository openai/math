import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContourForest
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyIncidence
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

/-! # The record contour on the assembled piece's port names

Reading a port name identifies the internal wire pairing with the opposite
in the record. Relabeling the vertex and forest permutations therefore gives
the same boundary walk and cycle cost in the assembly coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape

variable {K : ℕ} (R : PatchShape K)

/-- The recorded port rotation in internal wire and stub coordinates. -/
def pieceContourTurn : Perm ((R.toPiece.Edge × Bool) ⊕ R.Stub) :=
  R.endEquiv.symm.permCongr R.contourTurn

/-- The retained internal wire pairing in the piece coordinates. -/
def pieceForest : Perm ((R.toPiece.Edge × Bool) ⊕ R.Stub) :=
  R.endEquiv.symm.permCongr (swaps R.contourForest)

@[simp] theorem endEquiv_pieceContourTurn (x : (R.toPiece.Edge × Bool) ⊕ R.Stub) :
    R.endEquiv (R.pieceContourTurn x) = R.contourTurn (R.endEquiv x) :=
  R.endEquiv.apply_symm_apply _

@[simp] theorem endEquiv_pieceForest (x : (R.toPiece.Edge × Bool) ⊕ R.Stub) :
    R.endEquiv (R.pieceForest x) = swaps R.contourForest (R.endEquiv x) :=
  R.endEquiv.apply_symm_apply _

@[simp] theorem endEquiv_pieceContour (x : (R.toPiece.Edge × Bool) ⊕ R.Stub) :
    R.endEquiv ((R.pieceContourTurn * R.pieceForest) x) = R.contourPerm (R.endEquiv x) := by
  simp only [mul_apply, endEquiv_pieceContourTurn, endEquiv_pieceForest, contourPerm]

theorem endEquiv_insideMate (x : (R.toPiece.Edge × Bool) ⊕ R.Stub) :
    R.endEquiv (Equiv.sumCongr PortGraph.cross (Equiv.refl _) x) = R.opposite (R.endEquiv x) := by
  rcases x with ⟨e,(_|_)⟩ | s
  · rfl
  · exact (R.involutive e.val).symm
  · exact s.property.symm

/-- In a family of assembled records, the right-hand alternative is the action
of `StubPairing.insideMate` for this occurrence. -/
theorem pieceForest_sub (x : (R.toPiece.Edge × Bool) ⊕ R.Stub) :
    R.pieceForest x = x ∨ R.pieceForest x = Equiv.sumCongr PortGraph.cross (Equiv.refl _) x := by
  rcases R.contourForest_sub (R.endEquiv x) with h | h
  · exact Or.inl (R.endEquiv.injective ((R.endEquiv_pieceForest x).trans h))
  · exact Or.inr (R.endEquiv.injective ((R.endEquiv_pieceForest x).trans
      (h.trans (R.endEquiv_insideMate x).symm)))

/-- The relabeling identifies the support with the same set of numbered ports. -/
theorem pieceForest_support_card :
    R.pieceForest.support.card = (swaps R.contourForest).support.card := by
  apply Finset.card_bij' (fun x _ => R.endEquiv x) (fun y _ => R.endEquiv.symm y)
  · intro x hx
    exact mem_support.mpr (fun h => mem_support.mp hx
      (R.endEquiv.injective ((R.endEquiv_pieceForest x).trans h)))
  · intro y hy
    refine mem_support.mpr (fun h => mem_support.mp hy ?_)
    simpa only [endEquiv_pieceForest, apply_symm_apply] using congrArg R.endEquiv h
  · exact fun x _ => R.endEquiv.symm_apply_apply x
  · exact fun y _ => R.endEquiv.apply_symm_apply y

/-- Merging vertex cycles into the piece contours costs half the forest support. -/
theorem pieceForest_cycle_cost :
    2 * (cycles R.pieceContourTurn - cycles (R.pieceContourTurn * R.pieceForest)) =
      (R.pieceForest.support.card : ℤ) := by
  rw [cycles_equiv _ _ R.endEquiv R.endEquiv_pieceContourTurn,
    cycles_equiv _ _ R.endEquiv R.endEquiv_pieceContour, R.pieceForest_support_card]
  exact R.contourForest_cycle_cost

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
