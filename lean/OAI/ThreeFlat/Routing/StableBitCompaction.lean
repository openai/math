import OAI.ThreeFlat.Routing.StableCompactionOrder
import OAI.ThreeFlat.Routing.StableCompactionWiring
import OAI.ThreeFlat.Routing.BitonicSortNetwork

namespace OAI
/-! # An efficient bit network for stable compaction of a masked array -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.StableCompaction

/-- Pins are the mask, the source bits, and the proposed compacted array.
A disabled source slot may have either bit value. -/
def network (K : Type*) [Zero K] [One K] (m : ℕ) :
    BitNetwork K (2^m + (2^m + 2^m)) :=
  Wiring.network (BitonicSort.network K m (Wiring.width m))

theorem network_eval {K : Type*} [CommSemiring K] (m : ℕ) (M X Y : Fin (2^m) → Bool) :
    (network K m).eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0 := by
  have he := Wiring.network_eval (BitonicSort.network K m (Wiring.width m)) BitonicSort.sorted
    (BitonicSort.network_eval m (Wiring.width m)) M X Y
  have hout : (fun i => Wiring.payload
      (BitonicSort.sorted (Wiring.word (fun j => !(M j)) X) i)) = compact M X := by
    funext i
    exact masked_sorted M X i
  rwa [hout] at he

theorem network_cells (K : Type*) [Zero K] [One K] (m : ℕ) :
    (network K m).cells ≤ 16384 * 2^m * (m+1)^3 := by
  rw [network, Wiring.network_cells]
  apply (Nat.add_le_add_right (BitonicSort.network_cells K m _) _).trans
  simp only [Wiring.width, Wiring.rowCount]
  ring_nf
  omega

theorem network_internal (K : Type*) [Zero K] [One K] (m : ℕ) :
    (network K m).internal ≤ 16384 * 2^m * (m+1)^3 := by
  rw [network, Wiring.network_internal]
  apply (Nat.add_le_add_left (Nat.add_le_add_right (BitonicSort.network_internal K m _) _) _).trans
  change 2^m + Fintype.card (SortNetwork.Payload m (Wiring.width m)) + _ ≤ _
  simp only [SortNetwork.Payload, Fintype.card_prod, Fintype.card_fin, Wiring.width, Wiring.rowCount]
  ring_nf
  omega

end ThreeFlat.Routing.StableCompaction

end
end OAI
