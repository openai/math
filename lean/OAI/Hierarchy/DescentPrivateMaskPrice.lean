import OAI.Hierarchy.DescentPrivateHomeHardwareCost

namespace OAI
/-! # Complete price of the nine masked fields and terminal private exponent -/
namespace Hierarchy.DescentCompiler.TerminalScale

/-- The physical prefix prints one word per real mixed-radix table cell and one
word per mask channel. It precedes the already charged score lookup and scalar. -/
def privateMaskedClock (cells capacity homes blocks p : ℕ) :=
  (4+10*cells)+privateHomeClock capacity homes blocks p

def privateMaskedNames (cells capacity blocks p : ℕ) :=
  15*(cells+1)+privateHomeNames capacity blocks p

theorem masked_home_bill {cells capacity homes blocks p W T fund c : ℕ}
    (full : cells≤2*capacity+9*blocks) (live : 0<homes)
    (paid : privateHomeClock capacity homes blocks p*W*T≤357*c*fund) :
    (privateMaskedClock cells capacity homes blocks p+privateMaskedNames cells capacity blocks p)*W*T≤3213*c*fund := by
  have names:=home_names_le (capacity:=capacity) (blocks:=blocks) (p:=p) live
  have init : (4+10*cells)+15*(cells+1)≤5*privateHomeClock capacity homes blocks p := by
    unfold privateHomeClock
    have once : 16+234*blocks≤homes*(16+234*blocks) :=Nat.le_mul_of_pos_left _ live
    omega
  have assembled : privateMaskedClock cells capacity homes blocks p+privateMaskedNames cells capacity blocks p≤
      9*privateHomeClock capacity homes blocks p := by
    unfold privateMaskedClock privateMaskedNames
    omega
  calc
    _ ≤ (9*privateHomeClock capacity homes blocks p)*W*T :=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ assembled)
    _ = 9*(privateHomeClock capacity homes blocks p*W*T) := by ring
    _ ≤ 9*(357*c*fund) :=Nat.mul_le_mul_left _ paid
    _ = _ :=by ring

end Hierarchy.DescentCompiler.TerminalScale

end OAI
