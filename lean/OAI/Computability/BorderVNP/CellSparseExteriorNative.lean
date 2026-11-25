import OAI.Computability.BorderVNP.CellSparseExterior
import OAI.Computability.BorderVNP.CellPacketCopy
import OAI.Computability.BorderVNP.RoutingISARegisterFrame

/-! # Native serialization of a cell's sorted live exterior intervals

Registers 21 and 22 delimit the consecutive three-word descriptors. Register
23 holds the logical supplied width, registers 24 and 25 delimit the report
tail by base and length, and register 20 addresses the next output bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior.Native

open VPVNP.BurstRAM RationalHitting.StackLanguage CellPacketEncode

/-- The quotient loop writes a prefix-free gap count in little-endian order. -/
def gap : Code := .seq (.whileLt 0 16 (digit false)) CellPacketCopy.appendOne

/-- The live data is a prefix-free word even when it is empty. -/
def value : Code := .seq (CellPacketCopy.copy true) CellPacketCopy.appendOne

/-- Read one actual descriptor, determine the gap since the previous interval,
advance the descriptor address, and remember the new exclusive logical end. -/
def loadSpan : Code := .block [.load 27 21,.binary .add 21 21 1,.load 14 21,
  .binary .add 21 21 1,.load 28 21,.binary .add 21 21 1,.binary .add 15 14 28,
  .binary .sub 16 27 26,.binary .add 26 27 28]

/-- Emit one continuation marker, one gap and one actual live interval. -/
def span : Code := .seq loadSpan (.seq (emit false 1) (.seq gap value))

/-- Address the raw report tail and compute the final gap count. -/
def loadTail : Code := .block [.copy 14 24,.binary .add 15 24 25,.binary .sub 16 23 26]

/-- Terminate the interval list and transport the report bits in their original order. -/
def finish : Code := .seq loadTail (.seq (emit false 0) (.seq gap (CellPacketCopy.copy false)))

/-- Initialize the constants and empty logical prefix. -/
def initRegs : Code := .block [.constant 0 0,.constant 1 1,.constant 18 2,.constant 26 0]

/-- The complete exterior pass for one owned cell. -/
def write : Code := .seq initRegs (.seq (.whileLt 21 22 span) finish)

/-- The writer returns to its caller and performs ordinary unsigned steps only. -/
theorem ordinary : write.deterministic=true ∧ write.withoutAccept=true := by decide

/-- The outer scan can retain all of its state in the upper registers. -/
theorem keeps_high : ∀ j : Reg, 40 ≤ j.val → write.keeps j=true := by decide

/-- Exact effect of appending an uncompressed list of encoded output bits. -/
structure Output (input : NatState) (bits : List Bool) (z : NatState) : Prop where
  /-- Exclusive write position. -/
  cursor : z.reg 20 = input.reg 20 + bits.length
  /-- All of shared memory, including preservation outside the output interval. -/
  memory : z.mem = putDigits input.mem (input.reg 20) bits

theorem Output.append {u v z : NatState} {bs cs : List Bool} (hu : Output u bs v)
    (hv : Output v cs z) : Output u (bs++cs) z :=
  ⟨by rw [hv.cursor,hu.cursor,List.length_append,Nat.add_assoc],
   by rw [hv.memory,hu.memory,hu.cursor,putDigits_append]⟩

/-- The output interval remains disjoint from a later source interval when it
is split into a prefix and a suffix. -/
theorem split_apart {a n b k l : ℕ} (h : CompactWrite.Disjoint a n b (k+l)) :
    CompactWrite.Disjoint a n b k ∧ CompactWrite.Disjoint a n (b+k) l := by
  rcases h with h | h
  · exact ⟨Or.inl h,Or.inl (by omega)⟩
  · exact ⟨Or.inr (by omega),Or.inr (by omega)⟩

/-- Source words in a disjoint interval survive every emitted prefix. -/
theorem Output.unchanged {u z : NatState} {bs : List Bool} (effect : Output u bs z)
    {a n i : ℕ} (apart : CompactWrite.Disjoint a n (u.reg 20) bs.length) (hi : i<n) :
    z.mem (a+i)=u.mem (a+i) := by
  rw [effect.memory,putDigits_outside _ _ _ _ (by rcases apart with h | h <;> omega)]

end RoutingISA.SparseExterior.Native

end BorderVNP
end Computability
end OAI
