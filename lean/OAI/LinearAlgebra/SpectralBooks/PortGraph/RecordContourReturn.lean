import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordContourReturnForest
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContourWord
import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarReturnWord

/-! # First return of a numbered record in assembly coordinates

An assembly dart records its wire end or its stub name. Transporting the old
contour along that identification preserves its orientation. The literal first
return on the right summand is the cycle on the recorded list of stub names.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape

open PlanarSurgery
variable {K : ℕ} (R : PatchShape K)

theorem pieceContour_step (x : R.Dart) :
    R.endEquiv.symm (R.contourPerm x) = (R.pieceContourTurn * R.pieceForest) (R.endEquiv.symm x) := by
  simp [pieceContourTurn, pieceForest, contourPerm, Equiv.permCongr_apply, mul_apply]

/-- The assembled piece still has a single contour, with closing ports identified by name. -/
theorem pieceContour_sameCycle (hc : R.InternallyConnected) (x y : (R.Wire × Bool) ⊕ R.Stub) :
    (R.pieceContourTurn * R.pieceForest).SameCycle x y := by
  obtain ⟨a, rfl⟩ := R.endEquiv.symm.surjective x
  obtain ⟨b, rfl⟩ := R.endEquiv.symm.surjective y
  exact semiconj_perm_sameCycle R.pieceContour_step (R.contourPerm_sameCycle hc a b)

theorem pieceContour_covers (hc : R.InternallyConnected) (h : Nonempty R.Stub) :
    Covers (R.pieceContourTurn * R.pieceForest) Function.Embedding.inr :=
  fun x => ⟨h.some, R.pieceContour_sameCycle hc x _⟩

private theorem read_endEquiv (x : R.Dart) :
    ((R.endEquiv.symm x).getRight?).map Subtype.val = Option.guard (fun x => decide (R.opposite x = x)) x := by
  obtain ⟨z, rfl⟩ := R.endEquiv.surjective x
  rw [Equiv.symm_apply_apply]
  rcases z with ⟨e, (_ | _)⟩ | s
  · change none = Option.guard _ e.val
    simp [Option.guard, e.property.1]
  · change none = Option.guard _ (R.opposite e.val)
    have hne : R.opposite (R.opposite e.val) ≠ R.opposite e.val := by
      rw [R.involutive]
      exact e.property.1.symm
    simp [Option.guard, hne]
  · change some s.val = Option.guard _ s.val
    simp [Option.guard, s.property]

/-- Dropping the wire summand from the transported contour recovers the recorded names. -/
theorem pieceContour_read_word :
    (R.contourWord.map R.endEquiv.symm).filterMap Sum.getRight? = R.contourStubWord := by
  apply List.map_injective_iff.2 Subtype.val_injective
  rw [R.contourStubWord_values, List.filterMap_map, List.map_filterMap, ← List.filterMap_eq_filter]
  apply congrArg (fun f => List.filterMap f R.contourWord)
  funext x
  exact R.read_endEquiv x

/-- The positive first return on named stubs in the old assembled piece is
exactly the cyclic permutation of the canonical filtered word. -/
theorem pieceContour_onStubs (hc : R.InternallyConnected)
    (cover : Covers (R.pieceContourTurn * R.pieceForest) Function.Embedding.inr) :
    onStubs (R.pieceContourTurn * R.pieceForest) Function.Embedding.inr cover = R.contourStubWord.formPerm := by
  have h := R.contourWord_isBoundary.map _ R.endEquiv.symm.injective R.pieceContour_step
  have hr : Function.IsPartialInv (Sum.inr : R.Stub → (R.Wire × Bool) ⊕ R.Stub) Sum.getRight? := by
    intro s d
    exact Sum.getRight?_eq_some_iff.trans eq_comm
  have h' := onStubs_boundary_of_read _ Function.Embedding.inr cover _ hr h
  have hword := Eq.mp (congrArg (IsBoundary (onStubs _ _ cover)) R.pieceContour_read_word) h'
  exact Equiv.ext fun s => hword.turn _ (R.mem_contourStubWord hc s)

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
