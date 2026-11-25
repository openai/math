import OAI.Computability.NearSquareRoot.SynchronizedBatchWordSemantics
import OAI.Computability.NearSquareRoot.SynchronizedBatchMatching
import OAI.Computability.NearSquareRoot.SynchronizedPlacementRelabel
import OAI.Computability.NearSquareRoot.SynchronizedPlacedRoutes

/-! # Physical endpoints for a typed block instruction

The routing prefix uses the spectator fiber as its major index and the
within-half column as its minor index. Its endpoint numbers are precisely
the borrowing algorithm's padded row-major addresses.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.BatchWord

open Matrix SynchronizedBorrowing AxisWord
noncomputable section

variable {m : ℕ} (a c k : Fin m → ℕ) [∀ i, NeZero (a i)]
  (spectator : ∀ i, Spectators a c i ≃ Fin (Fintype.card (Spectators a c i)))
  (har : ∀ i, a i ≤ 2 ^ k i) (hborrow : ∀ i, 2 * 2 ^ k i ≤ 8 * a i)

abbrev Address := ∀ i, BlockAxis a c i
abbrev fiberCount (i : Fin m) := Fintype.card (Spectators a c i)

/-- Rank in the axis-specific order used for constructing a borrowing batch. -/
def axisRank (i : Fin m) : Address a c ≃ Fin (fiberCount a c i * (a i + c i)) :=
  (axisLayout a c spectator i).trans RoutingTable.rowMajor

include spectator in
theorem axisRank_card (i : Fin m) : fiberCount a c i * (a i + c i) = Fintype.card (Address a c) := by
  simpa using (Fintype.card_congr (axisRank a c spectator i)).symm

/-- All axes of this block have the same set of physical addresses. -/
def blockRank (i : Fin m) : Address a c ≃ Fin (Fintype.card (Address a c)) :=
  (axisRank a c spectator i).trans (finCongr (axisRank_card a c spectator i))

/-- Within a batch first enumerate spectator fibers, then the column within a half. -/
def pairLabels (i : Fin m) (b : Fin 15) :
    (Fin (2 ^ k i) × Fin (size (fiberCount a c i) b)) ≃ Fin (size (fiberCount a c i) b * 2 ^ k i) :=
  (Equiv.prodComm ..).trans finProdFinEquiv

/-- Embedding used by all opcodes of this batch, in the block's actual address type. -/
def batchEmbedding (i : Fin m) (b : Fin 15) :
    Ambient (k i) × Fin (size (fiberCount a c i) b) ↪ Address a c :=
  placementRelabel (auxiliaryLayout (har i)) (axisLayout a c spectator i) (batchCells (hborrow i) b)

/-- The instruction kernel places its local matrix in exactly these workspaces. -/
theorem gateMatrix_placed (i : Fin m) (b : Fin 15) (x : Inst) :
    gateMatrix a c k spectator har hborrow (i,b,x) =
      placeHom (batchEmbedding a c k spectator har hborrow i b) ((fixedSlot (a i) (k i) x).matrix dilationAddress) :=
  placeHom_relabel _ _ _ _

/-- The full matching table emitted by the numeric endpoint program starts
with exactly the endpoints used to lower the placed Walsh opcode. -/
theorem endpoints_apply (i : Fin m) (b : Fin 15) (u : Fin 2)
    (j : Fin (size (fiberCount a c i) b)) (v : Fin (2 ^ k i)) :
    (RoutedWalsh.endpoints dilationAddress (batchEmbedding a c k spectator har hborrow i b)
      (blockRank a c spectator i) (pairLabels a c k i b) (u,finProdFinEquiv (j,v))).val =
      RoutingTable.endpointValue (first (fiberCount a c i) b) (size (fiberCount a c i) b)
        (a i) (c i) (2 ^ k i) u.val j.val v.val := by
  rw [← RoutingTable.batchEndpoints_val (hborrow i) (har i) b u j v]
  simp [RoutedWalsh.endpoints, blockRank, axisRank, placementRelabel_apply, pairLabels,
    batchEmbedding, RoutingTable.batchEndpoints, batchCells]
  rfl

end
end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
