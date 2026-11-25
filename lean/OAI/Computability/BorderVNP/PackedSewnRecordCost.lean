import OAI.Computability.BorderVNP.PackedSewnRecordCompile
import OAI.Computability.BorderVNP.PackedSewnRecordMeasures
import OAI.Computability.BorderVNP.PackedFrozenCarryCost
import OAI.Computability.BorderVNP.PackedSewnFragmentJoin

/-! # Gate budget of the complete authentic exterior sewing record compiler

The compiler charges the given physical raw-fragment frame once. The remaining
terms account for sorting and merging the raw rectangle, two actual site
lookups, and writing both candidate opcodes on their shared scalar bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Sewn

open SewnField Shortening.PublicCapacity PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP.VerifierNetwork

variable {s n w R W : ℕ} {σ : Type*} [Fintype σ] (code : Fin s ↪ Fin (2^w))
    (raw : Frame σ (Fragment.Pin n w)) (col : Amounts s w → σ)

/-- Cost of the actual frame, uniformly bounded in the public word width and the
logarithm of the physical site-plus-fragment rectangle. -/
theorem tape_cubic (room : s+n+1 ≤ R) (logs : Nat.clog 2 R ≤ W) (bits : w ≤ W) :
    (tape code raw col).size ≤ raw.size + 27000*R*(W+1)^3 := by
  have hl := (Nat.clog_mono_right 2 (show s+n ≤ R by omega)).trans logs
  have small := (Nat.clog_mono_right 2 (show n ≤ R by omega)).trans logs
  have lookup := lookupCost_cubic s n w w W hl bits bits
  let unit := R*(W+1)^3
  have sort : 3000*(n+1)*(w+Nat.clog 2 n+1)^3 ≤ 24000*unit := by
    exact (Nat.mul_le_mul (Nat.mul_le_mul_left 3000 (show n+1 ≤ R by omega))
      (Nat.pow_le_pow_left (show w+Nat.clog 2 n+1 ≤ 2*(W+1) by omega) 3)).trans_eq (by dsimp [unit]; ring)
  have locations : 2*lookupCost s n w w ≤ 2000*unit :=
    (Nat.mul_le_mul_left 2 (lookup.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ room)))).trans_eq
      (by dsimp [unit]; ring)
  have fields : 2*n*(1+w)+9*n*w ≤ 11*R*(W+1) := by
    have h := (show n ≤ R by omega)
    apply (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h) (show 1+w ≤ W+1 by omega))
      (Nat.mul_le_mul (Nat.mul_le_mul_left 9 h) (show w ≤ W+1 by omega))).trans_eq
    ring
  have emit : (2*n*(1+w)+9*n*w)*(16*w+22) ≤ 242*unit := by
    have two : (W+1)^2 ≤ (W+1)^3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
    exact (Nat.mul_le_mul fields (show 16*w+22 ≤ 22*(W+1) by omega)).trans
      ((by ring : 11*R*(W+1)*(22*(W+1))=242*(R*(W+1)^2)).trans_le
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left R two)))
  apply (tape_size code raw col).trans
  rw [Nat.mul_assoc 27000]
  change _ ≤ raw.size+27000*unit
  omega

/-- Charge the two concrete fragment input rectangles and the complete sewing
compiler at the terminal schedule's actual lookup capacity. -/
theorem joined_tape_cubic {τ : Type} [Fintype τ] (shape : Shape) (cells original replicas tiles : ℕ)
    (sites : Fin shape.sites ↪ Fin (2^w))
    (wires : Frame τ (Fragment.Pin (2*shape.edges) w))
    (ports : Frame τ (Fragment.Pin (6*(replicas+1)*tiles) w)) (fields : Amounts shape.sites w → τ)
    (logs : Nat.clog 2 (routingRows shape cells original ((replicas+1)*tiles)) ≤ W) (bits : w≤W) :
    (tape sites (Fragment.joinFrame wires ports) fields).size ≤
      wires.size + ports.size + 27000*routingRows shape cells original ((replicas+1)*tiles)*(W+1)^3 := by
  simpa only [Fragment.joinFrame_size] using tape_cubic sites (Fragment.joinFrame wires ports) fields
    (fragment_slots_le shape cells original replicas tiles) logs bits

end Packing.Inherited.FrozenTape.Sewn

end BorderVNP
end Computability
end OAI
