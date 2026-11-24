import OAI.Computability.VPVNP.PrimedCounterRename
import OAI.Computability.VPVNP.PrimedStackRAMNodeRun

/-!
# Administrative calls of the scheduled pair parser

One clear call resets the leaf mark indexed by register 2. One initialization
call installs the root in the first frame and sets the depth to one. Each
comparison reads the dense production count and the corresponding nomination
word indexed by register 7. Every instruction in these calls is deterministic.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Admin

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM

/-- Include the eleven stack-parser operands in the first eleven positions of the fourteen-word
administrative operand table. -/
abbrev stackPublic (i : Fin 11) : Fin 14 := i.castLE (by decide)

/-- The original mark-clear block installed into the enlarged public-word table. -/
def clearOps : List (Op 16 14) := clearMark.map (renameOp id stackPublic)

/-- Instructions that write the root degree and state into the first pending frame and set the
stack depth to one. -/
def initOps : List (Op 16 14) :=
  [.publicWord 9 0, .publicWord 0 11, .write 9 0,
   .publicWord 9 1, .publicWord 1 12, .write 9 1,
   .publicWord 9 4, .constant 10 1, .write 9 10]

/-- Guard the dense label index, load its accumulated count and nominated count, and require
their equality. -/
def compareOps : List (Op 16 14) :=
  [.publicWord 11 10, .guardLt 7 11,
   .publicWord 9 3, .binary .add 9 9 7, .read 14 9,
   .publicWord 9 13, .binary .add 9 9 7, .read 15 9, .guardEq 14 15]

/-- Straight-line routine that clears the mark for one terminal position. -/
def clear : Flow 16 14 := lines clearOps (by decide)
/-- Straight-line routine that initializes the pending parse stack at the root of the current
site. -/
def init : Flow 16 14 := lines initOps (by decide)
/-- Straight-line routine checking the histogram count for one production against the
nomination. -/
def compare : Flow 16 14 := lines compareOps (by decide)

variable {w : ℕ} (pub : Fin 14 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w)

theorem clear_trace (hj : regs 2 < pub 6) :
    ∃ es rs, trace pub state clearOps regs mem = some (es, rs, writeMemory mem (pub 2 + regs 2) 0) ∧
      countProbes es = 1 ∧ es.length = 6 ∧ choiceBits es = [] := by
  change ∃ es rs, trace pub state
    [.publicWord 11 6, .guardLt 2 11, .publicWord 9 2, .binary .add 9 9 2,
     .constant 12 0, .write 9 12] regs mem = _ ∧ _
  simp (config := { decide := true }) [trace, Op.effect, BinaryOp.eval, hj, Function.update,
    countProbes, choiceBits]

theorem clear_reject (hj : ¬regs 2 < pub 6) : trace pub state clearOps regs mem = none := by
  change trace pub state
    [.publicWord 11 6, .guardLt 2 11, .publicWord 9 2, .binary .add 9 9 2,
     .constant 12 0, .write 9 12] regs mem = _
  simp (config := { decide := true }) [trace, Op.effect, hj, Function.update]

/-- External memory after storing the root degree, root state and initial stack depth at the
parser's public addresses. -/
def rootMemory (pub : Fin 14 → Word w) (mem : Memory w) : Memory w :=
  writeMemory (writeMemory (writeMemory mem (pub 0) (pub 11)) (pub 1) (pub 12)) (pub 4) 1

theorem init_trace :
    ∃ es rs, trace pub state initOps regs mem = some (es, rs, rootMemory pub mem) ∧
      countProbes es = 3 ∧ es.length = 9 ∧ choiceBits es = [] := by
  simp (config := { decide := true }) [initOps, rootMemory, trace, Op.effect, Function.update,
    countProbes, choiceBits]
  rfl

theorem compare_trace (hj : regs 7 < pub 10)
    (heq : mem (pub 3 + regs 7).val = mem (pub 13 + regs 7).val) :
    ∃ es rs, trace pub state compareOps regs mem = some (es, rs, mem) ∧
      countProbes es = 2 ∧ es.length = 9 ∧ choiceBits es = [] := by
  simp (config := { decide := true }) [compareOps, trace, Op.effect, BinaryOp.eval, hj, heq,
    Function.update, countProbes, choiceBits]

theorem compare_reject (h : ¬regs 7 < pub 10 ∨ mem (pub 3 + regs 7).val ≠ mem (pub 13 + regs 7).val) :
    trace pub state compareOps regs mem = none := by
  rcases h with h | h
  · simp (config := { decide := true }) [compareOps, trace, Op.effect, Function.update, h]
  · by_cases hj : regs 7 < pub 10 <;>
      simp (config := { decide := true }) [compareOps, trace, Op.effect, BinaryOp.eval, Function.update, h, hj]

end PrimedCounter.Admin

end VPVNP
end Computability
end OAI
