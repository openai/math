import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneAlgebra
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTriangleTable
import Mathlib.Data.Fintype.EquivFin

/-! # Pairing the state channels of a triangulated patch -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PlanarPatch

open scoped BigOperators

/-- A channel index records the two endpoint states of an edge. -/
def statePair (A B : Type*) [Fintype A] [Fintype B] :
    Fin (Fintype.card (A × B)) ≃ A × B := (Fintype.equivFin (A × B)).symm

variable {K : Type*} [CommSemiring K]

/-- The triangle contraction table on the numbered channels of the three edges. -/
def pairingTable {A : Type*} (B : Type*) {C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (E : A → C → K) : TriTable K (Fintype.card (A × C))
      (Fintype.card (A × B)) (Fintype.card (B × C)) :=
  fun u v w ↦ triangleTable E (statePair A C u) (statePair A B v) (statePair B C w)

/-- Contracting the two child channels sums exactly once over the middle state. -/
theorem triEval_pairingTable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (E : A → C → K) (V : A → B → K) (W : B → C → K) (u : Fin (Fintype.card (A × C))) :
    triEval (pairingTable B E) (fun v ↦ V (statePair A B v).1 (statePair A B v).2)
      (fun w ↦ W (statePair B C w).1 (statePair B C w).2) u =
      E (statePair A C u).1 (statePair A C u).2 *
        ∑ z : B, V (statePair A C u).1 z * W z (statePair A C u).2 := by
  rw [← contract_triangleTable E V W]
  unfold triEval pairingTable
  apply Fintype.sum_equiv (statePair A B)
  intro v
  apply Fintype.sum_equiv (statePair B C)
  intro w
  rfl

end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
