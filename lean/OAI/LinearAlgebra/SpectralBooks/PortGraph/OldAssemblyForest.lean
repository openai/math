import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordContourReturn
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyReturn

/-! # The forest and stub order of the reconstructed old map

The rotation of the old numbered map agrees with the rotation read in each
record. Its forest consists of the wires retained by the recorded Kruskal
order. Thus its returns to the stubs use the recorded positive boundary word.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {J A : Type} {K : ℕ} (R : J → PatchRecord K A)
    (connected : ∀ j, (R j).shape.InternallyConnected)

/-- Disk contours obtained from the sorted old records and their internal wires. -/
def diskData : StubPairing.PieceDiskData (pieces R) where
  turn j := (R j).shape.pieceContourTurn
  forest j := (R j).shape.pieceForest
  subpair j := (R j).shape.pieceForest_sub
  oneBoundary j := (R j).shape.pieceContour_sameCycle (connected j)
  cost j := by
    have h := (R j).shape.pieceForest_cycle_cost
    simp only [HyperbolicObstruction.PictureSwitch.cycles_eq_card_classes] at h ⊢
    convert! h using 1
    congr 3
    exact Subsingleton.elim _ _

theorem diskData_stubTurn (live : ∀ j, Nonempty (R j).shape.Stub) (j : J) :
    (diskData R connected).stubTurn (pieces R) live j = (R j).shape.contourStubWord.formPerm :=
  (R j).shape.pieceContour_onStubs (connected j) _

variable (C : StubPairing (fun j => (R j).shape.Stub)) [Fintype J]
    (r : vertices R) (hc : (graph R C).ConnectedFrom r)

/-- The reconstructed old map uses these same local rotations, including at
the original ends of cut wires. -/
theorem diskData_asMap_turn (x : C.Edge (pieces R) × Bool) :
    C.dartEquiv (pieces R) ((asMap R C r hc).num.turn x) =
      Equiv.sigmaCongrRight (diskData R connected).turn (C.dartEquiv (pieces R) x) :=
  dartEquiv_asMap_turn R C r hc x

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
