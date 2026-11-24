import OAI.Computability.VPVNP.PrimedStackRAMCode
import OAI.Computability.VPVNP.PrimedStackRAMLayout
import OAI.Computability.VPVNP.RAMRecords

/-!
# Constant-probe instructions for the primed parser

Registers 0 and 1 hold the current degree minus one and nonterminal state.
Register 2 holds a chosen location or split. Registers 3 and 4 hold child
states, 5 is the offset of the input row, 6 is the selected bit, and 7 is the
dense production index. The remaining registers are private temporaries.

Public words 0 through 4 are the degree-plane, state-plane, mark, histogram and
depth addresses. Words 5, 6, 7 are the stack capacity, number of positions and
number of states. Words 8, 9, 10 are the input base, terminal-label count and
total label count. These are public parameters of a fixed instruction table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM

/-- One straight-line instruction for the primed parser, with sixteen registers and eleven
public words. -/
abbrev Line := Op 16 11

/-- Push the frame in registers 0 and 1. The pointer records the next free slot. -/
def push : List Line :=
  [.publicWord 9 4, .read 8 9, .publicWord 11 5, .guardLt 8 11,
   .publicWord 11 0, .binary .add 11 11 8, .write 11 0,
   .publicWord 11 1, .binary .add 11 11 8, .write 11 1,
   .constant 10 1, .binary .add 8 8 10, .write 9 8]

/-- Pop the most recently pushed frame into registers 0 and 1. -/
def pop : List Line :=
  [.publicWord 9 4, .read 8 9, .constant 12 0, .guardLt 12 8,
   .constant 10 1, .binary .sub 8 8 10, .write 9 8,
   .publicWord 11 0, .binary .add 11 11 8, .read 0 11,
   .publicWord 11 1, .binary .add 11 11 8, .read 1 11]

/-- Reject a repeated leaf and mark its position otherwise. -/
def mark : List Line :=
  [.publicWord 11 6, .guardLt 2 11, .publicWord 9 2, .binary .add 9 9 2,
   .read 14 9, .constant 12 0, .guardEq 14 12, .constant 10 1, .write 9 10]

/-- Clear the indicated mark while preparing a fresh site. -/
def clearMark : List Line :=
  [.publicWord 11 6, .guardLt 2 11, .publicWord 9 2, .binary .add 9 9 2,
   .constant 12 0, .write 9 12]

/-- Fetch one bit of the assembled input row. -/
def leafBit : List Line :=
  [.publicWord 11 6, .guardLt 2 11, .publicWord 9 8, .binary .add 9 9 5,
   .binary .add 9 9 2, .read 6 9, .constant 13 2, .guardLt 6 13]

/-- Increment the word for a production. Reject an out-of-range label or a wrapped count. -/
def increment : List Line :=
  [.publicWord 11 10, .guardLt 7 11, .publicWord 9 3, .binary .add 9 9 7,
   .read 14 9, .constant 10 1, .binary .add 15 14 10, .guardLt 14 15, .write 9 15]

/-- Private arithmetic for the terminal production (state, position, bit). -/
def terminalIndex : List Line :=
  [.publicWord 11 6, .binary .mul 7 1 11, .binary .add 7 7 2,
   .constant 13 2, .binary .mul 7 7 13, .binary .add 7 7 6]

/-- Private arithmetic for the ordered binary production. Degree is positive
on entry, so its triangular prefix is degree times (degree minus one) divided by two. -/
def binaryIndex : List Line :=
  [.constant 10 1, .binary .sub 7 0 10, .binary .mul 7 7 0, .constant 13 2,
   .binary .div 7 7 13, .binary .add 7 7 2, .publicWord 11 7,
   .binary .mul 7 7 11, .binary .add 7 7 1, .binary .mul 7 7 11,
   .binary .add 7 7 3, .binary .mul 7 7 11, .binary .add 7 7 4,
   .publicWord 11 9, .binary .add 7 7 11]

variable {w : ℕ} (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w)

/-- The written degree, state and depth are exactly the three payloads of a push. -/
theorem push_spec (h : mem (pub 4).val < pub 5) :
    let depth := mem (pub 4).val
    let m' := writeMemory (writeMemory (writeMemory mem (pub 0 + depth) (regs 0))
      (pub 1 + depth) (regs 1)) (pub 4) (depth + 1)
    ∃ es rs, trace pub state push regs mem = some (es, rs, m') ∧
      countProbes es = 4 ∧ es.length = 13 ∧ rs 0 = regs 0 ∧ rs 1 = regs 1 := by
  simp (config := { decide := true }) [push, trace, Op.effect, BinaryOp.eval, h, Function.update,
    countProbes]
  rfl

theorem push_full (h : ¬mem (pub 4).val < pub 5) : trace pub state push regs mem = none := by
  simp (config := { decide := true }) [push, trace, Op.effect, h, Function.update]

/-- Popping reads the words at the previous top and decreases the depth. -/
theorem pop_spec (h : 0 < mem (pub 4).val) :
    let top := mem (pub 4).val - 1
    let m' := writeMemory mem (pub 4) top
    ∃ es rs, trace pub state pop regs mem = some (es, rs, m') ∧
      countProbes es = 4 ∧ es.length = 13 ∧ rs 0 = m' (pub 0 + top).val ∧
      rs 1 = m' (pub 1 + top).val := by
  simp (config := { decide := true }) [pop, trace, Op.effect, BinaryOp.eval, h, Function.update,
    countProbes]
  exact ⟨rfl, rfl, rfl⟩

theorem pop_empty (h : mem (pub 4).val = 0) : trace pub state pop regs mem = none := by
  simp (config := { decide := true }) [pop, trace, Op.effect, h, Function.update]

/-- The distinct-position test succeeds exactly on an unused position in range. -/
theorem mark_spec (h : regs 2 < pub 6) (hnew : mem (pub 2 + regs 2).val = 0) :
    ∃ es rs, trace pub state mark regs mem = some (es, rs, writeMemory mem (pub 2 + regs 2) 1) ∧
      countProbes es = 2 ∧ es.length = 9 ∧ rs 2 = regs 2 := by
  simp (config := { decide := true }) [mark, trace, Op.effect, BinaryOp.eval, h, hnew,
    Function.update, countProbes]
  rfl

theorem mark_reject (h : ¬regs 2 < pub 6 ∨ mem (pub 2 + regs 2).val ≠ 0) :
    trace pub state mark regs mem = none := by
  rcases h with h | h
  · simp (config := { decide := true }) [mark, trace, Op.effect, Function.update, h]
  · by_cases hi : regs 2 < pub 6 <;>
      simp (config := { decide := true }) [mark, trace, Op.effect, BinaryOp.eval, Function.update, hi, h]

theorem clearMark_spec (h : regs 2 < pub 6) :
    ∃ es rs, trace pub state clearMark regs mem = some (es, rs, writeMemory mem (pub 2 + regs 2) 0) ∧
      countProbes es = 1 ∧ es.length = 6 := by
  simp (config := { decide := true }) [clearMark, trace, Op.effect, BinaryOp.eval, h,
    Function.update, countProbes]

theorem leafBit_spec (h : regs 2 < pub 6) (hbit : mem (pub 8 + regs 5 + regs 2).val < 2) :
    ∃ es rs, trace pub state leafBit regs mem = some (es, rs, mem) ∧
      countProbes es = 1 ∧ es.length = 8 ∧ rs 6 = mem (pub 8 + regs 5 + regs 2).val := by
  simp (config := { decide := true }) [leafBit, trace, Op.effect, BinaryOp.eval, h, hbit,
    Function.update, countProbes]

theorem increment_spec (h : regs 7 < pub 10) (hcount : (mem (pub 3 + regs 7).val).val + 1 < 2^w) :
    let a := pub 3 + regs 7
    ∃ es rs, trace pub state increment regs mem = some (es, rs, writeMemory mem a (mem a.val + 1)) ∧
      countProbes es = 2 ∧ es.length = 9 ∧ (mem a.val + 1 : Word w).val = (mem a.val).val + 1 := by
  let v := mem (pub 3 + regs 7).val
  have he : (v + 1).val = v.val + 1 := Fin.val_add_one_of_lt' hcount
  have hlt : v < v + 1 := by change v.val < (v+1).val; omega
  change mem (pub 3 + regs 7).val < mem (pub 3 + regs 7).val + Fin.ofNat (2^w) 1 at hlt
  simp at hlt
  change (mem (pub 3 + regs 7).val + 1 : Word w).val = _ at he
  simp (config := { decide := true }) [increment, trace, Op.effect, BinaryOp.eval, h, hlt, he,
    Function.update, countProbes]
  exact ⟨rfl, rfl⟩

end PrimedStackRAM

end VPVNP
end Computability
end OAI
