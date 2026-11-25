import OAI.Computability.BorderVNP.PackedSewnTileViews
import OAI.Computability.BorderVNP.PackedFrozenLayerCost

/-! # The physical tile-fragment frame fits the sparse public circuit budget -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.Tile

open CellAddressCircuit Inherited.FrozenTape
open private view_cubic from OAI.Computability.BorderVNP.PackedFrozenLayerCost

variable {σ τ γ : Type} [Fintype σ] [Fintype τ] [Fintype γ]
variable {s m p m' p' C C' d d' k k' w slots R W : ℕ}
variable (F : Fields s m p C d k w σ) (B : Fields s m' p' C' d' k' w τ)
    (oldPin : σ → γ) (newPin : τ → γ) (hd : d≤w) (zero : γ)
    (rows : Fin slots → Option (Item p m' p'))

/-- Both true endpoint scans and every reserved probe fit a single linear
row factor times a cubic in the public binary word bound. -/
theorem physicalFrame_cubic (oldCount : 1+count s m p s ≤ R) (newCount : 1+count s m' p' s ≤ R)
    (slotCount : slots≤R) (width : w≤W) (newWidth : d'≤W) (depth : Nat.clog 2 R ≤ W) :
    (physicalFrame F B oldPin newPin hd zero rows).size ≤ 6500*R*(W+1)^3 := by
  have before := view_cubic F oldCount ⟨hd.trans width,width,depth⟩
  have after := view_cubic B newCount ⟨newWidth,width,depth⟩
  have per : (2+4*w)*(16*w+22) ≤ 100*(W+1)^3 := by
    calc _ ≤ (2+4*W)*(16*W+22) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have tail : slots*(2+4*w)*(16*w+22) ≤ 100*R*(W+1)^3 :=
    ((Nat.mul_assoc _ _ _).le.trans (Nat.mul_le_mul slotCount per)).trans_eq (by ring)
  calc _ ≤ _ := physicalFrame_size F B oldPin newPin hd zero rows
       _ ≤ 3200*R*(W+1)^3 + 3200*R*(W+1)^3 + 100*R*(W+1)^3 :=
         Nat.add_le_add (Nat.add_le_add before after) tail
       _ = _ := by ring

/-- The six genuine probes per team and tile already fit in the true final
endpoint-directory capacity. -/
theorem physical_slot_capacity {teams tiles old n : ℕ}
    (newCount : 1+count s (old+4*teams*tiles) n s ≤ R) : 6*teams*tiles ≤ R := by
  unfold count at newCount
  rw [Nat.mul_assoc 4] at newCount
  rw [Nat.mul_assoc 6]
  omega

end Packing.SewnField.Fragment.Tile

end BorderVNP
end Computability
end OAI
