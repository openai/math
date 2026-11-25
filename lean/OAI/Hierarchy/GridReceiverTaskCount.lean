import OAI.Hierarchy.GridReceiverLayoutScale
import Mathlib.Data.Fintype.Card

namespace OAI
/-! # Number of task words in the physical receiver election -/

namespace Hierarchy.GridReceiverDirectory
open ThreeFlat.Diagonal TraceAdmission

/-- Five words per elected task fit in sector 30 and all task ordinals fit
in one receiver workspace region. The list may be any actual election order. -/
theorem task_count {w N : ℕ} (age : 0<w) (count : N≤2^(3*w/5))
    (ids : List (Fin N)) (distinct : ids.Nodup) :
    5*ids.length≤2^(4*w) ∧ ids.length≤TickWorkspace.stride (receiverAge w) := by
  have n : ids.length≤N := by simpa using distinct.length_le_card
  have mono : ∀ {i j : ℕ}, i≤j → (2:ℕ)^i≤2^j := Nat.pow_le_pow_right (by decide)
  have l : ids.length≤2^w := (n.trans count).trans (mono (by omega))
  have low:=receiverAge_lower w
  constructor
  · calc
      _ ≤ 2^3*2^w := Nat.mul_le_mul (by decide) l
      _ = 2^(3+w) := (pow_add ..).symm
      _ ≤ _ := mono (by omega)
  · change ids.length≤(2^(receiverAge w)^10)^4
    rw [←pow_mul]
    exact l.trans (mono (by omega))

end Hierarchy.GridReceiverDirectory

end OAI
