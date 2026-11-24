import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish

/-! # Retaining the selected preimages below the output workspace

Each packed site's child ordinal is strictly below the common capacity
of a preimage row. Preserving memory through the end of the contiguous
count and row tables therefore preserves the full preimage directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression BurstRAM
open scoped Classical

variable {a g w : ℕ} (X : State a (packingLaneBits a g)) (term stride : Word w)

theorem preimages_retained {layout : Bool} {before after : Memory w}
    (h : ShrinkPreimages.Directory X layout (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) before)
    (frame : ∀ j < SelectedFinish.stop X term stride, after j = before j) :
    ShrinkPreimages.Directory X layout (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) after := by
  have length (v : Shrink.Packed X.Base a g) : (ShrinkPreimages.children X layout v).length = ShrinkPreimages.capacity a := by
    change Fintype.card {x : Shrink.Old X.Base a g // v = X.packingData.placement layout x} = _
    exact (Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => eq_comm))).trans
      (X.packingData.card_placement (by omega) layout v)
  have hcount : (SelectedFinish.counts X term stride).val ≤ SelectedFinish.countStart X term stride := Nat.mod_le ..
  have hrow : (SelectedFinish.rows X term stride).val ≤ SelectedFinish.rowStart X term stride := Nat.mod_le ..
  constructor
  · intro v
    have idx : (Shrink.packedIndex X.baseIndex v).val < ShrinkPreimages.newCount X := (Shrink.packedIndex X.baseIndex v).isLt
    rw [frame]; exact h.count v
    unfold SelectedFinish.stop SelectedFinish.rowStart; omega
  · intro v j
    have hj := j.isLt.trans_le (length v).le
    have hi := Nat.mul_le_mul_right (ShrinkPreimages.capacity a) (Shrink.packedIndex X.baseIndex v).isLt
    rw [Nat.succ_mul] at hi
    change _ ≤ ShrinkPreimages.newCount X * ShrinkPreimages.capacity a at hi
    rw [← ShrinkPreimages.oldCount_eq X] at hi
    rw [frame]; exact h.child v j
    unfold SelectedFinish.stop; omega

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
