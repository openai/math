import OAI.Computability.BorderVNP.PackedSewnWireImage
import OAI.Computability.BorderVNP.PackedFrozenLayerCost

/-! # Retained-wire fragment cost on the sparse pre-sewing and final rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open CellAddressCircuit Inherited Inherited.FrozenTape Diagonal.ExternalSew.FieldExport
open private view_cubic from OAI.Computability.BorderVNP.PackedFrozenLayerCost
open scoped Classical

variable {s m n M N C k w : ℕ} {σ τ : Type} [Fintype σ] [Fintype τ]
variable (F : Fields s m n C w k w σ) (B : Fields s M N C w k w τ)
variable (old : σ → τ) (present : Fin m → σ) (retained : Fin m → Fin M)

/-- The two site-local scans and one fixed gate row per candidate endpoint
consume a linear number of rectangles times a cubic in the public word width. -/
theorem frame_cubic {R W : ℕ} (before : 1+count s m n s ≤ R) (after : 1+count s M N s ≤ R)
    (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    (frame F B old present retained).size ≤ 6800*R*(W+1)^3 := by
  have a := view_cubic F before ⟨width,width,depth⟩
  have b := view_cubic B after ⟨width,width,depth⟩
  have rows : 2*m ≤ R := by unfold count at before; omega
  have per : (2+4*w)*(60*w+20) ≤ 400*(W+1)^3 := by
    calc _ ≤ (2+4*W)*(60*W+20) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le W,Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have total := frame_size F B old present retained
  have tail : (2*m)*(2+4*w)*(60*w+20) ≤ 400*R*(W+1)^3 :=
    ((Nat.mul_assoc _ _ _).le.trans (Nat.mul_le_mul rows per)).trans_eq (by ring)
  calc _ ≤ _ := total
       _ ≤ (3200*R*(W+1)^3)+(3200*R*(W+1)^3)+(400*R*(W+1)^3) :=
         Nat.add_le_add (Nat.add_le_add a b) tail
       _ = _ := by ring

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
