import OAI.Computability.BorderVNP.PackedBottomReports

/-! # Relocating the two address windows of a supplemental report record -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse

/-- The source work and the use suffix can move by independent offsets. A
physical supplemental row still makes exactly the same comparison as the
birth site's private view, including each bit of the unused zero suffix. -/
theorem reportRows_rebase_iff (birth physical : ℕ → Bool) (boxes : List (List Factor))
    (base orig cap copies cursor realCursor : ℕ) (fs : List Factor) (fit : count fs ≤ cap)
    (workAt : ∀ (i : Fin copies) (k : Fin (bottomStride orig cap)),
      physical (base+i.val*bottomStride orig cap+k.val) = birth (i.val*bottomStride orig cap+k.val))
    (use : ∀ (i : Fin copies) (k : Fin (count fs)),
      birth (cursor+k.val*copies+i.val) = physical (realCursor+k.val*copies+i.val)) :
    (∀ r ∈ reportRows 0 orig cap copies cursor fs, r.Valid boxes birth) ↔
      ∀ r ∈ reportRows base orig cap copies realCursor fs, r.Valid boxes physical := by
  rw [reportRows_valid _ _ _ _ _ _ _ _ fit, reportRows_valid _ _ _ _ _ _ _ _ fit]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  have src := workAt ⟨i,hi⟩ ⟨orig+k,Nat.add_lt_add_left hk orig⟩
  simp only [Nat.zero_add,Nat.add_assoc] at src ⊢
  rw [src]
  by_cases live : k < count fs
  · have read := use ⟨i,hi⟩ ⟨k,live⟩
    simpa only [stageValue,live,ite_true,Nat.add_assoc] using
      (Iff.of_eq (congrArg (birth (i*bottomStride orig cap+(orig+k)) = ·) read))
  · simp [stageValue,live]

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
