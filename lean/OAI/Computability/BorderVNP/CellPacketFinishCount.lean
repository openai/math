import OAI.Computability.BorderVNP.RoutingISACompactFrame
import OAI.Computability.BorderVNP.RoutingISATableState
import Mathlib.Data.Nat.ModEq

/-! # Computing a packed descriptor's burst length in fixed-width registers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open VPVNP.BurstRAM

private theorem length_pack_split {w : ℕ} (hw : 0 < w) (xs : List Bool) :
    (CompactFrame.pack w xs).length = xs.length / w + xs.length / w + 1 +
      (if xs.length % w < w - xs.length % w then 0 else 1) := by
  rw [CompactFrame.length_pack, show 2 * xs.length + 1 + w - 1 = xs.length + xs.length + w by omega,
    Nat.add_div_right _ hw]
  have rem := Nat.mod_lt xs.length hw
  by_cases carry : xs.length % w < w - xs.length % w
  · rw [ite_eq_left carry, Nat.add_div_eq_of_add_mod_lt (by omega : xs.length % w + xs.length % w < w)]
  · rw [ite_eq_right carry, Nat.add_div_eq_of_le_mod_add_mod (by omega : w ≤ xs.length % w + xs.length % w) hw]

/-- Count the framed words by doubling the quotient of the payload length and comparing
the remainder with its complement. The full framed bit length need never fit in a register. -/
def countBurst : Code := .block [.constant 1 1, .binary .div 15 4 2, .binary .mod 16 4 2,
  .binary .sub 17 2 16, .binary .add 15 15 15, .binary .add 15 15 1,
  .ifLt 16 17 .nop (.binary .add 15 15 1)]

/-- The native counter returns the packed length while preserving the burst base and memory.
Only the final length must fit, even if twice the original bit length overflows. -/
theorem countBurst_run {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    (s : Bank w) (m : Memory w) (payload : List Bool) (hw : 0 < w)
    (width : readings s 2 = w) (length : readings s 4 = payload.length)
    (fit : (CompactFrame.pack w payload).length < 2^w) :
    BoundedRun pub macros countBurst s m 9 (fun z =>
      z.reg 15 = (CompactFrame.pack w payload).length ∧ z.reg 5 = readings s 5 ∧ z.mem = readings m) := by
  rw [length_pack_split hw] at fit ⊢
  have one := Nat.one_lt_two_pow hw.ne'
  have rem := Nat.mod_lt payload.length hw
  by_cases carry : payload.length % w < w - payload.length % w <;>
    simp only [carry, ↓reduceIte, Nat.add_zero] at fit ⊢
  all_goals
    have safe : countBurst.fixedSafe w (readings pub) (.ofWords s m) := by
      simp (config := {decide := true}) [countBurst, Code.block, Code.fixedSafe, Code.fixedEval,
        Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, NatState.ofWords, length, width, carry]
      omega
    apply (countBurst.runFixed pub macros s m safe).mono le_rfl
    rintro _ rfl
    simp (config := {decide := true}) [countBurst, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, length, width, carry]

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
