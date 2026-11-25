import OAI.Computability.BorderVNP.PackedSewnPhysicalOperands
import OAI.Computability.BorderVNP.PackedSewnTileCost
import OAI.Computability.BorderVNP.PackedSewnWireCost

/-! # The gate and slot charge of both physical exterior operand passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Grid

open Crossing Inherited TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Fragment.Tile CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
set_option quotPrecheck false

variable {R r t pins link inner n V groups copies old : ℕ} {E : Type}
    (G : Wiring R r t pins link inner n E) (hV : 0 < V) (count : groups*copies = R+1)
    (hg : 0 < blockWidth (r*n) V) (small : blockWidth (r*n) V ≤ link)
local notation "g" => blockWidth (r*n) V
local notation "w₀" => G.program.length+t
open private tile_room from OAI.Computability.BorderVNP.PackedSewnTileSemantic
local notation "room" => tile_room G hV
local notation "params" => (⟨R,r,w₀,link,g,V⟩ : FieldExport.Params)

variable {σ : Type} [Fintype σ] {s C k w : ℕ} (F : Fields s old (groups*V) C w k w σ)
    (name : ℕ → ℕ → ℕ) (present : Fin old → σ)
local notation "B" => FieldExport.fields F params name
local notation "tileRows" => Fragment.Tile.slot count old hg small room

/-- Both the retained cable ends and all six candidate tile fragments fit in the single
post-sew physical row-count budget, including zero-width and unused slots. -/
theorem physicalOperands_slots {s old teams tiles n A : ℕ}
    (after : 1 + CellAddressCircuit.count s (old+4*teams*tiles) n s ≤ A) :
    2*old+6*teams*tiles ≤ A := by
  unfold CellAddressCircuit.count at after
  rw [Nat.mul_assoc 4] at after
  rw [Nat.mul_assoc 6]
  omega

/-- The entire raw source of the exterior emitter has linear row cost and a cubic word
factor, including all four true endpoint scans and all positive or padded row tests. -/
theorem physicalOperands_cubic {A W : ℕ}
    (before : 1+CellAddressCircuit.count s old (groups*V) s ≤ A)
    (after : 1+CellAddressCircuit.count s (old+4*(R+1)*V) ((R+1)*V) s ≤ A)
    (width : w ≤ W) (depth : Nat.clog 2 A ≤ W) :
    (physicalOperands G hV count hg small F name present).size ≤ 13300*A*(W+1)^3 := by
  have oldCost := WireFragments.frame_cubic F B Sum.inl present (WireFragments.retainedRow old (params).slots)
    before after width depth
  have newCost := Fragment.Tile.physicalFrame_cubic F B Sum.inl id le_rfl (.inr false) tileRows before after
    (Fragment.Tile.physical_slot_capacity after) width width depth
  rw [physicalOperands,Fragment.joinFrame_size]
  exact (Nat.add_le_add oldCost newCost).trans_eq (by ring)

end Packing.SewnField.Grid

end BorderVNP
end Computability
end OAI
