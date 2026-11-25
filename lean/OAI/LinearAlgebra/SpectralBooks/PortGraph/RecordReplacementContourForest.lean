import OAI.LinearAlgebra.SpectralBooks.PortGraph.RecordReplacementContour
import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarForestEuler

/-! # The forest involution of a numbered patch record

Each retained band pairs two numbered ports of an actual internal wire.
Its two ports contribute one to the drop in the number of vertex cycles.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

namespace PortGraph.PatchShape

variable {K : ℕ} (R : PatchShape K)

private theorem opposite_sq : R.opposite * R.opposite = 1 :=
  Equiv.ext R.involutive

private theorem paired_of_mem_contourForest (ab : R.Dart × R.Dart) (h : ab ∈ R.contourForest) :
    R.opposite ab.1 = ab.2 :=
  ((R.mem_contourPairs).mp ((forestEdges_sublist _ _).subset h)).2.2

/-- The forest crosses a recorded internal wire or fixes the dart. -/
theorem contourForest_sub (x : R.Dart) :
    swaps R.contourForest x = x ∨ swaps R.contourForest x = R.opposite x :=
  PlanarSurgery.swaps_paired_sub R.opposite R.opposite_sq _ R.paired_of_mem_contourForest x

/-- The boundary port names are fixed by the forest involution. -/
@[simp] theorem contourForest_stub (x : R.Stub) : swaps R.contourForest x.val = x.val :=
  (R.contourForest_sub x.val).elim id (fun h => h.trans x.property)

/-- Crossing a retained band twice returns to the original numbered port. -/
theorem contourForest_sq : swaps R.contourForest * swaps R.contourForest = 1 :=
  PlanarSurgery.swaps_paired_sq R.opposite R.opposite_sq _ R.paired_of_mem_contourForest

/-- Every merger of two vertex cycles accounts for both ports of one retained band. -/
theorem contourForest_cycle_cost :
    2 * (cycles R.contourTurn - cycles R.contourPerm) = ((swaps R.contourForest).support.card : ℤ) := by
  have hs := PlanarSurgery.forest_support_card_of_sq R.contourTurn R.contourPairs R.contourForest_sq
  have hc := forestEdges_cycles R.contourTurn (SameCycle.setoid R.contourTurn) le_rfl R.contourPairs
  change (swaps R.contourForest).support.card = 2 * R.contourForest.length at hs
  change cycles R.contourPerm = cycles R.contourTurn - R.contourForest.length at hc
  omega

end PortGraph.PatchShape

end

end SpectralBooks
end LinearAlgebra
end OAI
