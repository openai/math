import OAI.ThreeFlat.Diagonal.SlotImage
import OAI.ThreeFlat.Diagonal.CompressorRefreshGraph

namespace OAI
/-! # All six columns under disjoint concatenation of regular slots -/
namespace ThreeFlat.Diagonal.CompressorRefresh
open Computability.VPVNP.Compression
variable {V L : Type*} {a b N Z : ℕ} (A : LiftedSlots V a L) (B : LiftedSlots V b L)

def leftRow (p : V × Fin a) : V × Fin (a+b) := (slotCases V a b).symm (.inl p)
def rightRow (p : V × Fin b) : V × Fin (a+b) := (slotCases V a b).symm (.inr p)

theorem oriented_left (rev : Bool) (p : V × Fin a) :
    SlotImage.oriented (union A B) rev (leftRow (b:=b) p) =
      leftRow (SlotImage.oriented A rev p) := by
  cases rev with
  | false => exact unionTarget_left _ _ _
  | true =>
    apply (union A B).base.target.injective
    change (union A B).base.target ((union A B).base.target.symm _) =
      unionTarget A.base B.base ((slotCases V a b).symm (.inl (A.base.target.symm p)))
    rw [Equiv.apply_symm_apply,unionTarget_left,Equiv.apply_symm_apply,leftRow]

theorem oriented_right (rev : Bool) (p : V × Fin b) :
    SlotImage.oriented (union A B) rev (rightRow (a:=a) p) =
      rightRow (SlotImage.oriented B rev p) := by
  cases rev with
  | false => exact unionTarget_right _ _ _
  | true =>
    apply (union A B).base.target.injective
    change (union A B).base.target ((union A B).base.target.symm _) =
      unionTarget A.base B.base ((slotCases V a b).symm (.inr (B.base.target.symm p)))
    rw [Equiv.apply_symm_apply,unionTarget_right,Equiv.apply_symm_apply,rightRow]

theorem shift_left (rev : Bool) (p : V × Fin a) :
    SlotImage.shift (union A B) rev (leftRow (b:=b) p)=SlotImage.shift A rev p := by
  have disp (q : V × Fin a) : (union A B).displacement (leftRow (b:=b) q) = A.displacement q := by
    simp [union,leftRow]
  cases rev with
  | false => exact disp p
  | true =>
    change (union A B).displacement (SlotImage.oriented (union A B) true (leftRow p)) = _
    rw [oriented_left]
    exact disp _

theorem shift_right (rev : Bool) (p : V × Fin b) :
    SlotImage.shift (union A B) rev (rightRow (a:=a) p)=SlotImage.shift B rev p := by
  have disp (q : V × Fin b) : (union A B).displacement (rightRow (a:=a) q) = B.displacement q := by
    simp [union,rightRow]
  cases rev with
  | false => exact disp p
  | true =>
    change (union A B).displacement (SlotImage.oriented (union A B) true (rightRow p)) = _
    rw [oriented_right]
    exact disp _

theorem fields_left (base : V ≃ Fin N) (lane : L ≃ Fin Z) (p : V × Fin a) (rev : Bool) :
    SlotImage.fields (union A B) base lane (leftRow (b:=b) p) rev =
      SlotImage.fields A base lane p rev := by
  unfold SlotImage.fields
  rw [oriented_left,shift_left]
  rfl

theorem fields_right (base : V ≃ Fin N) (lane : L ≃ Fin Z) (p : V × Fin b) (rev : Bool) :
    SlotImage.fields (union A B) base lane (rightRow (a:=a) p) rev =
      ![SlotImage.fields B base lane p rev 0,a+SlotImage.fields B base lane p rev 1,
        SlotImage.fields B base lane p rev 2] := by
  unfold SlotImage.fields
  rw [oriented_right,shift_right]
  rfl

end ThreeFlat.Diagonal.CompressorRefresh

end OAI
