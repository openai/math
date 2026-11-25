import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementTemplate
import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordContourSmallReturn
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyReturn

/-! # The disk certificate of each actual replacement term

The local rotation comes from the template's numbered ports and the forest
uses every internal edge of the selected tree. The first return to named
stubs is precisely the old record's contour in either branch.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
namespace PortGraph.PatchShape.RecordTerm

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch PlanarSurgery
open PlanarPatch UniformDecorations ReplacementTemplate

variable {K w : ℕ} {F : Type} [Field F] {R : PatchShape K} {hc : R.InternallyConnected}
  (u : R.RecordTerm hc w F)

abbrev Dart := (u.piece.Edge × Bool) ⊕ R.Stub

/-- Rotation at the numbered ports of the actual selected term. -/
def turn : Perm u.Dart := u.piece.slotTurn u.slotEquiv

/-- All internal wires of the replacement tree are retained in its disk. -/
def mate : Perm u.Dart := Equiv.sumCongr PortGraph.cross (Equiv.refl _)

private theorem turn_direct (small : Fintype.card R.Stub ≤ 3) :
    (direct (hc := hc) (w := w) (F := F) small).turn = R.singleTurn := R.singleTurn_numbered hc

private theorem turn_pruned {b : ℕ} (total : Fintype.card R.Stub = b+1) (large : 3 ≤ b)
    (t : TrivalentTree (MvPolynomial (UniformDecorations.Address w) F) (fun _ : R.Stub => 2^w) (2^w))
    (labels : t.labels = (List.finRange b).map (fun i => (R.contourSlots hc total).symm i.castSucc))
    (bd n c) :
    (pruned total large t labels bd n c).turn =
      t.namedTurn (rootMem total large t labels) (stubEquiv total t labels).symm :=
  t.slotTurn_eq_namedTurn (rootMem total large t labels) (stubEquiv total t labels).symm

/-- Cutting through every internal edge leaves just one boundary cycle. -/
theorem contour_sameCycle (a b : u.Dart) : (u.turn * u.mate).SameCycle a b := by
  cases u with
  | direct small =>
    rw [turn_direct]
    exact R.singleContour_sameCycle hc a b
  | pruned total large t labels bd n c =>
    rw [turn_pruned]
    exact t.sameCycle_namedContour _ _ a b

private theorem transportCost {A : Type*} {d₁ d₂ : DecidableEq A} {f₁ f₂ : Fintype A}
    {p q : Perm A}
    (h : 2 * (@cycles A d₁ f₁ p - @cycles A d₁ f₁ (p*q)) = ((@support A d₁ f₁ q).card : ℤ)) :
    2 * (@cycles A d₂ f₂ p - @cycles A d₂ f₂ (p*q)) = ((@support A d₂ f₂ q).card : ℤ) := by
  obtain rfl : d₁ = d₂ := Subsingleton.elim _ _
  obtain rfl : f₁ = f₂ := Subsingleton.elim _ _
  exact h

/-- Euler cost of the full replacement tree, counting both ends of each wire. -/
theorem contour_cost :
    2 * (cycles u.turn - cycles (u.turn * u.mate)) = (u.mate.support.card : ℤ) := by
  cases u with
  | direct small =>
    rw [turn_direct]
    exact transportCost R.singleContour_cost
  | pruned total large t labels bd n c =>
    rw [turn_pruned]
    exact transportCost (t.namedForest_euler (rootMem total large t labels) (stubEquiv total t labels).symm)

/-- Deleting the internal darts from the disk boundary keeps exactly the
canonical cyclic word of the old patch. -/
theorem contour_onStubs (cover : Covers (u.turn * u.mate) (.inr : R.Stub ↪ u.Dart)) :
    onStubs _ _ cover = R.contourStubWord.formPerm := by
  cases u with
  | direct small =>
    revert cover
    rw [turn_direct]
    intro cover
    exact R.singleContour_onStubs cover
  | pruned total large t labels bd n c =>
    revert cover
    rw [turn_pruned]
    intro cover
    exact (t.onStubs_namedContour (rootMem total large t labels) _
      (stubNames_complete total t labels).1 (stubNames_complete total t labels).2).trans
        (formPerm_labels total t labels)

section Family

variable {J : Type} {S : J → PatchShape K} {conn : ∀ j, (S j).InternallyConnected}
  (U : ∀ j, (S j).RecordTerm (conn j) w F)

/-- A mixed family of genuine replacement terms has the assembled disk certificate. -/
def pieceDiskData : StubPairing.PieceDiskData (fun j => (U j).piece) where
  turn j := (U j).turn
  forest j := (U j).mate
  subpair _ _ := Or.inr rfl
  oneBoundary j := (U j).contour_sameCycle
  cost j := transportCost (U j).contour_cost

/-- The certificate's local turn agrees with the actual piece numbering. -/
theorem pieceTurn_eq (j : J) :
    StubPairing.pieceTurn (fun j => (U j).piece) (fun j => (U j).numbering) j =
      (pieceDiskData U).turn j :=
  (StubPairing.pieceTurn_eq_slotTurn (fun i => (U i).piece) (fun i => (U i).numbering) j).trans
    ((U j).piece.slotTurn_finCongr (U j).slotEquiv _)

/-- Returning to a live patch's boundary recovers the old record order. -/
theorem pieceDiskData_stubTurn (live : ∀ j, Nonempty (S j).Stub) (j : J) :
    (pieceDiskData U).stubTurn _ live j = (S j).contourStubWord.formPerm :=
  (U j).contour_onStubs _

end Family
end PortGraph.PatchShape.RecordTerm

end

end SpectralBooks
end LinearAlgebra
end OAI
