import OAI.Computability.BorderVNP.TeamOpcode

/-!
# Fixed instruction tables for the packed evaluator

Straight-line statements, conditionals, binary choices, and bounded loops
compile to the finite team instruction set. The emitted table and all of its
jump targets are independent of the input length and of every runtime word.
Arithmetic, memory probes, and private macro calls occupy individual opcodes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Register bank shared by all fragments of the packed evaluator. -/
abbrev Reg := Fin 64

/-- Fixed public operand indices. Runtime arrays reside in addressed memory. -/
abbrev Arg := Fin 32

/-- Fixed entry points for read-only private routines. -/
abbrev Macro := Fin 8

/-- Structured assembly on the ordinary signed team opcodes. No statement
takes a function of the runtime word bank or shared memory as its operand. -/
inductive Code where
  | nop
  | constant (dst : Reg) (value : Word 8)
  | publicWord (dst : Reg) (arg : Arg)
  | copy (dst src : Reg)
  | binary (op : BinaryOp) (dst x y : Reg)
  | load (dst addr : Reg)
  | store (addr src : Reg)
  | sign (negative : Bool)
  | call (routine : Macro) (addr len : Reg)
  | reject
  | accept
  | seq (first second : Code)
  | ifEq (x y : Reg) (yes no : Code)
  | ifLt (x y : Reg) (yes no : Code)
  | choose (yes no : Code)
  | whileLt (x y : Reg) (body : Code)

/-- A straight-line or branching block whose statements share the same bank. -/
def Code.block : List Code → Code
  | [] => .nop
  | [x] => x
  | x :: y :: tail => .seq x (.block (y :: tail))

/-- The number of fixed opcode slots before the fragment's continuation. -/
def Code.slots : Code → ℕ
  | .seq a b => a.slots + b.slots
  | .ifEq _ _ a b | .ifLt _ _ a b | .choose a b => 1 + a.slots + b.slots
  | .whileLt _ _ a => 1 + a.slots
  | _ => 1

/-- Every statement, including the empty block, has an actual entry slot. -/
theorem Code.slots_pos (c : Code) : 0 < c.slots := by
  induction c <;> simp only [slots] <;> omega

/-- The ordinary opcode and its optional signed/private extension at one PC. -/
abbrev Line (p : ℕ) := Instr 8 p 64 32 × TeamOpcode.Tag p 64 8

/-- Resolve structured labels relative to the start of a fragment and emit one
actual instruction. A sequence exits its first part directly into its second. -/
def Code.emit {p : ℕ} (label : ℕ → Fin p) (pc start finish : ℕ) : Code → Line p
  | .nop => (.jumpEq 0 0 (label finish) (label finish), .native)
  | .constant d v => (.constant d v (label finish), .native)
  | .publicWord d i => (.publicWord d i (label finish), .native)
  | .copy d s => (.copy d s (label finish), .native)
  | .binary op d x y => (.binary op d x y (label finish), .native)
  | .load d a => (.readExternal d a (label finish), .native)
  | .store a s => (.writeExternal a s (label finish), .native)
  | .sign b => (.reject, .sign b (label finish))
  | .call j a l => (.reject, .call j a l (label finish))
  | .reject => (.reject, .native)
  | .accept => (.accept, .native)
  | .seq a b =>
    if pc < start + a.slots then a.emit label pc start (start + a.slots)
    else b.emit label pc (start + a.slots) finish
  | .ifEq x y a b =>
    if pc = start then (.jumpEq x y (label (start+1)) (label (start+1+a.slots)), .native)
    else if pc < start + 1 + a.slots then a.emit label pc (start+1) finish
    else b.emit label pc (start+1+a.slots) finish
  | .ifLt x y a b =>
    if pc = start then (.jumpLt x y (label (start+1)) (label (start+1+a.slots)), .native)
    else if pc < start + 1 + a.slots then a.emit label pc (start+1) finish
    else b.emit label pc (start+1+a.slots) finish
  | .choose a b =>
    if pc = start then (.choose (label (start+1)) (label (start+1+a.slots)), .native)
    else if pc < start + 1 + a.slots then a.emit label pc (start+1) finish
    else b.emit label pc (start+1+a.slots) finish
  | .whileLt x y body =>
    if pc = start then (.jumpLt x y (label (start+1)) (label finish), .native)
    else body.emit label pc (start+1) start

/-- The final program counter accepts normal fall-through from the complete table. -/
def Code.row (c : Code) (pc : Fin (c.slots + 1)) : Line (c.slots + 1) :=
  if pc.val < c.slots then c.emit (fun j ↦ ⟨min j c.slots, by omega⟩) pc.val 0 c.slots
  else (.accept, .native)

/-- Compile the length-independent control graph to the same table the signed
physical processor dispatcher fetches. -/
def Code.program (c : Code) : TeamOpcode.Program (c.slots + 1) 64 32 8 where
  base := { literalWidth := 8, entry := 0, code := fun pc ↦ (c.row pc).1 }
  tag := fun pc ↦ (c.row pc).2

/-- The final fall-through instruction of the emitted table really accepts. -/
theorem Code.fetch_finish (c : Code) {w : ℕ} (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (regs : Reg → Word w) :
    c.program.fetch pub macros ⟨Fin.last c.slots, regs⟩ = .accept := by
  simp [program, row, TeamOpcode.Program.fetch, TeamOpcode.enabled, TeamOpcode.permitted,
    TeamOpcode.divisor, Instr.resize, Instr.runLogged, Instr.run, CallAction.mapState, TeamOpcode.nativeAction]

/-- Read a frame word at `public[0]+field` using an address and constant scratch
register. The frame is shared addressed memory, so dynamically computed values
come from actual earlier stores. -/
def readFrame (dst address scratch : Reg) (field : Word 8) : Code :=
  .block [.publicWord address 0, .constant scratch field, .binary .add address address scratch,
    .load dst address]

/-- Store a frame word through the same fixed addressing convention. -/
def writeFrame (src address scratch : Reg) (field : Word 8) : Code :=
  .block [.publicWord address 0, .constant scratch field, .binary .add address address scratch,
    .store address src]

end RoutingISA

end BorderVNP
end Computability
end OAI
