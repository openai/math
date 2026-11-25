import OAI.Computability.BorderVNP.RoutingISAHeader
import OAI.Computability.BorderVNP.RoutingISAAddressProof

/-! # The first unused position of an incident routing block

The padding scan begins after the broadcast header and the two directed legs.
Its initialization reads the occupied lengths from two row-major table entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

/-- The ten statements preceding the inner padding scan in the non-self branch. -/
def paddingStartSteps : List Code := [
  pairAddress 13 2 11 3 19, .load 16 13, pairAddress 13 11 2 3 19, .load 17 13,
  .binary .add 10 6 16, .ifLt 10 6 .reject .nop,
  .binary .add 18 10 17, .ifLt 18 10 .reject .nop, .copy 10 18, .ifLt 7 10 .reject .nop]

/-- Execute the two table reads and all three capacity checks. -/
def paddingStartBlock : Code := .block paddingStartSteps

/-- Header length followed by the forward and reverse leg lengths at this partner. -/
def paddingOffset (mem : ℕ → ℕ) (s : Reg → ℕ) : ℕ :=
  s 6 + mem (pairIndex (s 19) (s 3) (s 2) (s 11)) +
    mem (pairIndex (s 19) (s 3) (s 11) (s 2))

/-- The table lookups and arithmetic all fit in the word, and every rejection
test falls through, when the two legs fit in the incident block. -/
theorem paddingStart_safe {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (forwardRoom : pairIndex (s 19) (s 3) (s 2) (s 11) < 2^w)
    (reverseRoom : pairIndex (s 19) (s 3) (s 11) (s 2) < 2^w)
    (fits : paddingOffset mem s ≤ s 7) (blockRoom : s 7 < 2^w) :
    paddingStartBlock.safeReadOnly w pub mem s := by
  simp only [paddingOffset, pairIndex] at forwardRoom reverseRoom fits
  simp (config := { decide := true }) [paddingStartBlock, paddingStartSteps, Code.block, pairAddress,
    Code.safeReadOnly, Code.evalNat, addressOp, addressOpFits]
  omega

private theorem guard_eval (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) (a b : Reg) :
    (Code.ifLt a b .reject .nop).evalNat pub mem s = s := by
  by_cases h : s a < s b <;> simp [Code.evalNat, h]

/-- The resulting cursor points to the first position outside the header and both legs. -/
theorem paddingStart_cursor (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) :
    paddingStartBlock.evalNat pub mem s 10 = paddingOffset mem s := by
  simp only [paddingStartBlock, paddingStartSteps, Code.block, pairAddress, Code.evalNat.eq_7, guard_eval]
  simp (config := { decide := true }) [Code.evalNat, addressOp, paddingOffset, pairIndex]

/-- Every register other than the address, two loaded widths, cursor, and temporary
sum retains its incoming value. -/
theorem paddingStart_preserves (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ) (i : Reg)
    (h10 : i ≠ 10) (h13 : i ≠ 13) (h16 : i ≠ 16) (h17 : i ≠ 17) (h18 : i ≠ 18) :
    paddingStartBlock.evalNat pub mem s i = s i := by
  simp only [paddingStartBlock, paddingStartSteps, Code.block, pairAddress, Code.evalNat.eq_7, guard_eval]
  simp (config := { decide := true }) [Code.evalNat, h10, h13, h16, h17, h18]

end RoutingISA

end BorderVNP
end Computability
end OAI
