import OAI.Computability.VPVNP.PrimedCounterAdmin
import OAI.Computability.VPVNP.PrimedCounterCall
import OAI.Computability.VPVNP.PrimedCounterCursor
import OAI.Computability.VPVNP.PrimedInputRAMOpcodes
import OAI.Computability.VPVNP.PrimedInputRAMPortCode

/-!
# Fixed native program for one primed pair

The absolute cursor is tested against the end of the two input rectangles,
then against the end of the site parses. In a site block, division computes
the row and remainder distinguishes a mark clear, root initialization, or
node visit. The final region reads and compares one histogram entry per call.
Four private registers hold the cursor, its successor, the call count, and a
phase boundary outside the operand ranges of the embedded routines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Program

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

/-- Structured control flow for the combined counter using 52 private registers and 34 public
operands. -/
abbrev Code := PrimedInputRAM.Flow 52 34
/-- Register indices in the combined counter, including the four registers reserved beyond the
input assembler. -/
abbrev Reg := Fin 52
/-- Indices of the input, parser and schedule operands in the combined public-word vector. -/
abbrev Pub := Fin 34

/-- Identify each of the 48 input-assembler registers with the same-numbered combined register. -/
def inputReg (i : Fin 48) : Reg := i.castAdd 4
/-- Identify each of the sixteen parser registers with the same-numbered combined register. -/
def parserReg (i : Fin 16) : Reg := i.castAdd 36
/-- Place the sixteen assembler operands at the beginning of the combined public-word vector. -/
def inputPub (i : Fin 16) : Pub := i.castAdd 18
/-- Place the fourteen parser operands after the assembler operands in the combined public-word
vector. -/
def parserPub (i : Fin 14) : Pub := (i.castAdd 4).natAdd 16
/-- Address a stack-parser operand through the parser's block in the combined public-word
vector. -/
def stackPub (i : Fin 11) : Pub := parserPub (Admin.stackPublic i)

/-- Injective register placement used to link the input-assembly code into the combined
counter. -/
def inputRegs : Fin 48 ↪ Reg := ⟨inputReg, fun _ _ h => Fin.ext (congrArg (fun j : Reg => j.val) h)⟩
/-- Injective register placement used to link the parser and its administrative routines into
the combined counter. -/
def parserRegs : Fin 16 ↪ Reg := ⟨parserReg, fun _ _ h => Fin.ext (congrArg (fun j : Reg => j.val) h)⟩

/-- The whole body is finite and independent of every pair-specific header. -/
def input : Code := renameFlow inputReg inputPub (Opcodes.dataCall PortCode.program)
/-- The grammar-node visit routine installed on the combined registers and stack-parser
operands. -/
def node : Code := renameFlow parserReg stackPub nodeFlow
/-- The mark-clearing routine installed in the combined parser code. -/
def clear : Code := renameFlow parserReg parserPub Admin.clear
/-- The root-frame initialization routine installed in the combined parser code. -/
def init : Code := renameFlow parserReg parserPub Admin.init
/-- The nominated-versus-accumulated production count check installed in the combined parser
code. -/
def compare : Code := renameFlow parserReg parserPub Admin.compare

/-- Register 51 contains the end of the assembly calls on entering this block.
The quotient is the zero-based row number and the remainder is the in-row cursor. -/
def rowSetup : List (Op 52 34) :=
  [.binary .sub 18 48 51, .publicWord 19 31, .binary .div 20 18 19,
   .binary .mod 21 18 19, .publicWord 22 (stackPub 6)]

/-- Decode the site and local slot from the cursor and invoke mark clearing, root setup or the
grammar-node visit. -/
def site : Code := .seq (lines rowSetup (by decide)) <|
  .ifLt 21 22 (.seq (.line (.copy 2 21)) clear) <|
  .ifEq 21 22 init (.seq (.line (.binary .mul 5 20 22)) node)

/-- Dispatch post-assembly cursors to a site parse or, after the site region ends, a histogram
comparison. -/
def afterInputs : Code := .seq (.line (.publicWord 17 32)) <|
  .ifLt 48 17 site (.seq (.line (.binary .sub 7 48 17)) compare)

/-- Load the current cursor from persistent state, compute its successor and read the total and
input-assembly boundaries. -/
def dispatchSetup : List (Op 52 34) :=
  [.stateWord 48, .constant 51 1, .binary .add 49 48 51, .publicWord 50 33, .publicWord 51 30]

/-- Execute one scheduled counter call by dispatching its absolute cursor to the input or
post-assembly code. -/
def body : Code := .seq (lines dispatchSetup (by decide)) (.ifLt 48 51 input afterInputs)

/-- A single table is instantiated at every `n`, degree/state range, group pair
and nomination. It returns register 49, or accepts when that equals register 50. -/
def table := Call.template body 49 50

/-- Operand table for the common program. Input parameters, parser parameters,
and four schedule bounds occupy consecutive fixed slots. -/
def publicWords {w : ℕ} (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (assembly S m nodes T : ℕ) : Pub → Word w :=
  Fin.append inputs (Fin.append parser
    ![(assembly : Word w), (Cursor.span m nodes : Word w), (Cursor.compareStart assembly S m nodes : Word w),
      (Cursor.calls assembly S m nodes T : Word w)])

theorem public_input {w : ℕ} (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (A S m nodes T : ℕ) (i : Fin 16) : publicWords inputs parser A S m nodes T (inputPub i) = inputs i :=
  Fin.append_left ..

theorem public_parser {w : ℕ} (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (A S m nodes T : ℕ) (i : Fin 14) : publicWords inputs parser A S m nodes T (parserPub i) = parser i := by
  rw [publicWords, parserPub, Fin.append_right, Fin.append_left]

theorem public_schedule {w : ℕ} (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (A S m nodes T : ℕ) :
    let pub := publicWords inputs parser A S m nodes T
    pub 30 = (A : Word w) ∧ pub 31 = (Cursor.span m nodes : Word w) ∧
      pub 32 = (Cursor.compareStart A S m nodes : Word w) ∧ pub 33 = (Cursor.calls A S m nodes T : Word w) := by
  dsimp only
  have hh (j : Fin 4) : publicWords inputs parser A S m nodes T ((j.natAdd 14).natAdd 16) =
      (![(A : Word w), ↑(Cursor.span m nodes), ↑(Cursor.compareStart A S m nodes),
        ↑(Cursor.calls A S m nodes T)] : Fin 4 → Word w) j := by
    rw [publicWords, Fin.append_right, Fin.append_right]
  exact ⟨hh 0, hh 1, hh 2, hh 3⟩

theorem table_literalWidth : table.literalWidth = 2 := rfl

end PrimedCounter.Program

end VPVNP
end Computability
end OAI
