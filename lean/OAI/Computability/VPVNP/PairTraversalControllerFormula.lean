import OAI.Computability.VPVNP.CompressorRecordRegisterSetup
import OAI.Computability.VPVNP.PairTraversalOnlineWorker

/-!
# Runtime operands for the post-calendar traversal controller

One persistent word encodes the phase, physical level and site number. The
first pass writes every role. The second pass writes every descriptor. Each
burst reads its operands directly from the terminal and level headers.
All expression trees are fixed and use the repository's native compiler.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController

open BurstRAM BurstRAM.PrivateRAM CompressorRecords PhaseRecipe TraversalRows OnlineWorker
open scoped Fin.CommRing

/-- The virtual five-word recipe ABI names the public square base and its
radix exponent. The last of the six input registers holds the true state word. -/
def recipePub {w : ℕ} (pub : Fin 11 → Word w) : Fin 5 → Word w :=
  ![pub 2, pub 7, pub 2, pub 2, pub 2]

/-- Recover the high terminal header by adding the square workspace size to its base and
subtracting the 32-word header reservation. -/
def terminal : Expr :=
  let radix := Expr.binary .shiftLeft (.lit 1) (.publicWord 1)
  ((Expr.publicWord 0).add (radix.mul radix)).sub (.lit 32)

/-- Read the specified scalar word from the terminal header computed by the traversal recipe. -/
def term (field : ℕ) : Expr := .load (terminal.add (.lit field))
/-- Read a field from level j using the terminal header's first-level pointer and level pitch. -/
def level (j : Expr) (field : ℕ) : Expr :=
  .load (((term 16).add (j.mul (term 17))).add (.lit field))

/-- The terminal-header expression for the number of physical traversal levels. -/
def levels : Expr := term 1

/-- Initial site count used by the controller, with the terminal site count selected when the
directory contains only the initial level. -/
def initialSites : Expr :=
  let initial := level (.lit 0) 21
  initial.add (((Expr.lit 1).div levels).mul ((term 7).sub initial))

/-- Width of one phase-level block in the persistent state encoding, one larger than the
initial site count. -/
def pitch : Expr := initialSites.add (.lit 1)
/-- Decode the combined traversal phase and level ordinal by dividing the persistent state by
the phase-level pitch. -/
def phaseLevel : Expr := Expr.state.div pitch
/-- Decode the within-level site ordinal as the remainder of the persistent state modulo the
pitch. -/
def site : Expr := Expr.state.mod pitch
/-- Physical level ordinal obtained by reducing the combined phase-level number modulo the
level count. -/
def index : Expr := phaseLevel.mod levels
/-- Word-valued nonzero test on the current level ordinal, implemented by division by itself. -/
def positiveIndex : Expr := index.div index
/-- Preceding level ordinal, saturating at zero so the initial level remains a valid header
address. -/
def previous : Expr := index.sub positiveIndex

/-- Select the current level's site count from the initial count or the preceding pass's output
count. -/
def count : Expr := initialSites.add (positiveIndex.mul ((level previous 22).sub initialSites))

/-- Register order for control comparisons, state returns, and the three workers. -/
def formulas : Fin 18 → Expr :=
  ![site, phaseLevel, levels, levels.add levels, count, index, .lit 0, Expr.state.add (.lit 1),
    (phaseLevel.add (.lit 1)).mul pitch, term 14, level index 14, term 15, level index 27,
    level (.lit 0) 14, level previous 24, level previous 25, level previous 26, level previous 14]

/-- Registers for the setup compiler followed by seven worker scratch words
and three readonly public/state inputs. -/
abbrev R := RegisterSetup.regCount formulas + 10

/-- Embed the expression-evaluation registers in the leading portion of the traversal
controller register bank. -/
def vm : Fin (RegisterSetup.regCount formulas) ↪ Fin R := Fin.castAddEmb 10
/-- Register containing the evaluated result of the given traversal operand formula. -/
def value (i : Fin 18) : Fin R := vm (RegisterSetup.output formulas i)
/-- A register beyond the formula evaluator, indexed among the ten extra traversal worker and
input registers. -/
def extra (i : Fin 10) : Fin R := i.natAdd (RegisterSetup.regCount formulas)
/-- Assign the five public recipe operands and persistent state input to the extra controller
registers, reusing the workspace base where prescribed. -/
def inputs : Fin 6 → Fin R := ![extra 7, extra 8, extra 7, extra 7, extra 7, extra 9]

theorem inputs_apart (i : Fin 6) (j : Fin (RegisterSetup.regCount formulas)) : inputs i ≠ vm j := by
  have apart (t : Fin 10) : extra t ≠ vm j := by
    intro e
    have h := congrArg Fin.val e
    change RegisterSetup.regCount formulas + t.val = j.val at h
    omega
  fin_cases i <;> apply apart

/-- Embed the seven worker scratch registers in the controller bank after the register
evaluator. -/
def scratchRegs : Fin 7 ↪ Fin R := (Fin.castAddEmb 3).trans (Fin.natAddEmb _)

private theorem value_outside (i : Fin 18) : value i ∉ Set.range scratchRegs := by
  rintro ⟨j, h⟩
  have he := congrArg Fin.val h
  change RegisterSetup.regCount formulas + j.val = (RegisterSetup.output formulas i).val at he
  have := (RegisterSetup.output formulas i).isLt
  omega

/-- Construct the worker's register allocation from the designated formula outputs for its
public bank and current site. -/
def allocation (fields : Fin 6 → Fin 18) : Allocation R where
  scratch := scratchRegs
  bank := value ∘ fields
  site := value 0
  bankOutside := fun i => value_outside (fields i)
  siteOutside := value_outside _

/-- Formula-output indices supplying the role writer's offset, row base, pitch, role code, and
unused zero fields. -/
def roleFields : Fin 6 → Fin 18 := ![9, 10, 11, 12, 6, 6]
/-- Formula-output indices supplying the leaf-row writer's base and pitch, with zero values in
unused fields. -/
def leafFields : Fin 6 → Fin 18 := ![13, 11, 6, 6, 6, 6]
/-- Formula-output indices supplying the fiber count and row arrays, row capacity, preceding
row base, current row base, and pitch. -/
def fiberFields : Fin 6 → Fin 18 := ![14, 15, 16, 17, 10, 11]

/-- The role-tag worker's register allocation using its selected traversal formula outputs. -/
abbrev roleAlloc := allocation roleFields
/-- The leaf-row worker's register allocation using the initial layer base and row pitch. -/
abbrev leafAlloc := allocation leafFields
/-- The fiber-row worker's register allocation using the selected placement directory and old
and new row bases. -/
abbrev fiberAlloc := allocation fiberFields

end PairSimulation.TraversalController

end VPVNP
end Computability
end OAI
