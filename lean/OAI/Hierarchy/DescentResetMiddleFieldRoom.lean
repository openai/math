import OAI.Hierarchy.DescentResetMiddleCalendar
import OAI.Hierarchy.DescentClosedReset

namespace OAI
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle

theorem fieldWidth_wide (D cap n k Ht : ℕ) {r : ℕ} (hr : r ≤ k) :
    max (max r (2^n)) (2^r) < 2^(fieldWidth D cap n k Ht) ∧ n < fieldWidth D cap n k Ht := by
  have rk : r < fieldWidth D cap n k Ht := by unfold fieldWidth; omega
  have nk : n < fieldWidth D cap n k Ht := by unfold fieldWidth; omega
  have rp : 2^r < 2^(fieldWidth D cap n k Ht) := Nat.pow_lt_pow_right (by decide) rk
  have np : 2^n < 2^(fieldWidth D cap n k Ht) := Nat.pow_lt_pow_right (by decide) nk
  exact ⟨max_lt (max_lt (Nat.lt_two_pow_self.trans rp) np) rp, nk⟩

end Hierarchy.DescentDatedAddressBook.ResetMiddle

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDatedAddressBook

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}

/-- The actual reset board and residual key fit the numeric field of the scheduled middle page. -/
theorem original_middle_field_room (B : ClosedReset input ctl) (degree cap Ht : ℕ) :
    let r := B.reset.k-B.terminals.commonDepth
    let field := ResetMiddle.fieldWidth degree cap n k Ht
    max (max r (2^B.reset.n)) (2^r) < 2^field ∧ B.reset.n < field := by
  dsimp only
  rw [B.dimension, B.keyWidth, B.commonDepth, Nat.add_sub_cancel_left]
  exact ResetMiddle.fieldWidth_wide degree cap n k Ht le_rfl

end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
