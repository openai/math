import OAI.Computability.VPVNP.PrimedInputRAMFlowRun
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Fixed word code for the two input passes

The persistent cursor ranges first over the chosen-bit rectangle, then over
the assembled-input rectangle. A common dispatch computes the bit's source
and its owner flag. The port arithmetic routine supplies the sender site and
within-port offset. All other field handling, including the three supplied
cut lengths, is given by the explicit word instructions below.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Structured word code for the primed input passes, with 48 private registers and 16 public
words. -/
abbrev Code := PrimedInputRAM.Flow 48 16
/-- Index of a private register in the primed input dispatcher. -/
abbrev Reg := Fin 48
/-- Index of a public parameter word of the primed input dispatcher. -/
abbrev Pub := Fin 16

/-- Code for a single arithmetic or word-memory instruction. -/
def line (op : Op 48 16) : Code := .line op

/-- Load a two-bit literal into the destination register. -/
def set (dst : Reg) (value : Word 2) := line (.constant dst value)
/-- Load the indexed public word into a private register. -/
def load (dst : Reg) (j : Pub) := line (.publicWord dst j)
/-- Apply a binary word operation to two registers and store its result in the destination
register. -/
def bin (op : BinaryOp) (dst x y : Reg) := line (.binary op dst x y)
/-- Copy a word by adding the source to register 0, which the parameter loader initializes to
zero. -/
def copy (dst src : Reg) := bin .add dst src 0
/-- Read an external word at the address held in a register into the destination register. -/
def read (dst addr : Reg) := line (.read dst addr)
/-- Write the source register's word to the external address held in the address register. -/
def write (addr src : Reg) := line (.write addr src)

/-- Straight sequence of instructions or structured blocks. -/
def sequence (first : Code) (rest : List Code) : Code := rest.foldl Flow.seq first

/-- Constants, public geometry, persistent cursor, and the pair-specific
cut lengths supplied by the three external header words. -/
def parameterTail : List (Op 48 16) :=
  [.constant 1 1, .constant 2 2, .constant 3 3, .stateWord 4, .publicWord 5 0,
    .publicWord 6 1, .publicWord 7 2, .publicWord 8 3, .publicWord 9 4, .publicWord 10 5,
    .publicWord 11 6, .publicWord 12 7, .publicWord 13 8, .publicWord 14 9, .publicWord 15 10,
    .publicWord 16 11, .publicWord 17 12, .read 18 0, .read 19 1, .read 20 2]

/-- Initialize the constants, load the persistent cursor and public layout words, then read the
three cut lengths from external memory. -/
def loadParameters : Code := parameterTail.foldl (fun a op ↦ .seq a (.line op)) (set 0 0)

/-- Registers 21 through 24 hold the flat index, group, site and within-row
offset. Register 29 is the next persistent cursor and 30 is the output
address of the current pass. -/
def unpackCursor : Code := sequence (bin .mod 21 4 5)
  [bin .div 31 21 6, bin .div 22 31 7, bin .mod 23 31 7, bin .mod 24 21 6,
    bin .add 29 4 1, bin .add 30 11 4]

/-- Result registers are 26 (address or bit), 27 (fetch flag), 28 (owner
flag). Writing all three on each branch also covers a missing or padded bit. -/
def literalZero : Code := sequence (set 26 0) [set 27 0, set 28 0]

/-- Extract the indicated bit by shifting and masking, then mark the result as a literal
without a first-pass choice. -/
def literalBit (src amount : Reg) : Code := sequence (bin .shiftRight 26 src amount)
  [bin .bitAnd 26 26 1, set 27 0, set 28 0]

/-- Run the supplied address computation and flag the result as a memory fetch, recording
whether this cell owns a first-pass choice. -/
def fetched (addressCode : Code) (own : Bool) : Code :=
  sequence addressCode [set 27 1, set 28 (if own then 1 else 0)]

/-- Fetch the index bit of this very group, with zero beyond the supplied
fixed length. Header bit arrays start immediately after the length words. -/
def indexField : Code := .ifLt 23 14
  (fetched (sequence (bin .mul 26 22 14) [bin .add 26 26 23, bin .add 26 26 3]) false)
  literalZero

/-- Compute the fixed base `3 + 2*indexLength` of the advice array. -/
def adviceBase : Code := sequence (bin .mul 26 2 14) [bin .add 26 26 3]

/-- Resolve the site's advice bit to its header address within the supplied advice length, and
to a literal zero beyond it. -/
def adviceField : Code := .ifLt 23 15
  (fetched (sequence adviceBase [bin .add 26 26 23]) false) literalZero

/-- Resolve an incoming outer cut bit using the left cut length and its header offset
immediately after the advice. -/
def leftField : Code := .ifLt 23 18
  (fetched (sequence adviceBase [bin .add 26 26 15, bin .add 26 26 23]) false) literalZero

/-- Resolve an outgoing outer cut bit using the right cut length and its header offset beyond
the reserved left cut array. -/
def rightField : Code := .ifLt 23 20
  (fetched (sequence adviceBase [bin .add 26 26 15, bin .add 26 26 16, bin .add 26 26 23]) false)
  literalZero

/-- A middle cut bit is read from the first group's outgoing slot. -/
def middleField (own : Bool) : Code := .ifLt 23 19
  (fetched (sequence (bin .mul 26 23 6)
    [bin .add 26 26 11, bin .add 26 26 12, bin .add 26 26 8, bin .add 26 26 3]) own)
  literalZero

/-- Dispatch the four one-bit fields using their offset in register 25. -/
def headerFields : Code :=
  .ifEq 25 0 indexField (.ifEq 25 1 adviceField
    (.ifEq 25 2 (.ifEq 22 0 leftField (middleField false)) (.ifEq 22 0 (middleField true) rightField)))

/-- Translate a raw transcript sender into its chosen-bit scratch address.
The port routine sets registers 32 (present), 33 (sender), 34 (offset). -/
def portResult : Code := .ifEq 32 0 literalZero
  (sequence (bin .mul 26 22 7) [bin .add 26 26 33, bin .mul 26 26 6, bin .add 26 26 11,
    bin .add 26 26 12, bin .add 26 26 8, bin .add 26 26 3, bin .add 26 26 1, bin .add 26 26 34,
    set 27 1, .ifEq 23 33 (.ifEq 25 34 (set 28 1) (set 28 0)) (set 28 0)])

/-- Extract the address bit or identify one of the fixed-width header/port
intervals by comparisons against their exclusive ends. Register 35 holds
a temporary boundary; the port block can reuse it after entering. -/
def dispatch (port : Code) : Code := .ifLt 24 12 (literalBit 17 24)
  (sequence (bin .add 35 12 8) [
    .ifLt 24 35 (sequence (bin .sub 25 24 12) [literalBit 23 25])
      (sequence (bin .sub 25 24 35) [bin .add 35 35 3, bin .add 35 35 1,
        .ifLt 24 35 headerFields
          (sequence (bin .sub 25 24 35) [bin .add 35 35 13,
            .ifLt 24 35 (sequence port [portResult]) literalZero])])])

/-- A designated cell has two different paths even if the stored value
already equals the chosen value. A nondesignated cell takes only the
deterministic skip. Second-pass cells always write one output word. -/
def act : Code := .ifLt 4 5
  (.ifEq 28 1 (.branch (write 30 1) (write 30 0)) (set 28 0))
  (.ifEq 27 1 (sequence (read 26 26) [write 30 26]) (write 30 26))

/-- Fixed body of a data call. Its exit register is 29. The terminal cursor
may enter the next phase of the auxiliary machine. -/
def dataCall (port : Code) : Code := sequence loadParameters [unpackCursor, dispatch port, act]

/-- A physical opcode table with constant instruction count across lengths
when the port block is fixed. -/
def table (port : Code) := (dataCall port).template (some 29)

/-- The template executes the control graph with the true burst interpreter
for every raw memory and branch stream. -/
theorem table_executes (port : Code) {w : ℕ} (pub : Pub → Word w) (state : Word w)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) :
    let cmd := dataCall port
    let M := (table port).instantiate w pub
    execute M.program fuel (M.program.start state) mem bits =
      Flow.run cmd pub state
        (fun left rs mem' bs => execute M.program left ⟨cmd.exitPC,state,rs,fun _ => 0⟩ mem' bs)
        fuel cmd.entry (fun _ => 0) mem bits :=
  Flow.template_executes (dataCall port) (some 29) pub state mem bits fuel

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
