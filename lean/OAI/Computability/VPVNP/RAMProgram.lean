import OAI.Computability.VPVNP.RAMExecution

/-!
# Elementary programs for the burst RAM

A fixed finite instruction table and finite public constants specify the private
word computation of a call in Lemma 10.1. Register operands and instruction
destinations are bounded indices into the fixed machine. Private and external
addresses are full words. Private memory and registers start at zero on each
call, while the persistent input is separately available to its instructions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open VPVNP.BurstRAM

/-- Arithmetic uses reduction modulo the word modulus. Division and remainder
use Lean's natural-number conventions on a zero divisor. Shifts by at least
the word width have value zero. -/
inductive BinaryOp where
  | add | sub | mul | div | mod | bitAnd | bitOr | bitXor | shiftLeft | shiftRight
  deriving DecidableEq

variable {w p r k : ℕ}

/-- Evaluate a binary arithmetic or bitwise opcode on width-w words. Arithmetic results are
word-sized, and a shift by at least the word width yields zero. -/
def BinaryOp.eval : BinaryOp → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y
  | .div, x, y => Fin.ofNat _ (x.val / y.val)
  | .mod, x, y => Fin.ofNat _ (x.val % y.val)
  | .bitAnd, x, y => Fin.ofNat _ (x.val &&& y.val)
  | .bitOr, x, y => Fin.ofNat _ (x.val ||| y.val)
  | .bitXor, x, y => Fin.ofNat _ (x.val ^^^ y.val)
  | .shiftLeft, x, y => if y.val < w then Fin.ofNat _ (x.val <<< y.val) else 0
  | .shiftRight, x, y => if y.val < w then Fin.ofNat _ (x.val >>> y.val) else 0

/-- Each instruction has constant arity. The conditional tests and branch
choices designate two program counters; every other continuing instruction
designates one. -/
inductive Instr (w p r k : ℕ) where
  | constant (dst : Fin r) (value : Word w) (next : Fin p)
  | publicWord (dst : Fin r) (index : Fin k) (next : Fin p)
  | stateWord (dst : Fin r) (next : Fin p)
  | copy (dst src : Fin r) (next : Fin p)
  | binary (op : BinaryOp) (dst lhs rhs : Fin r) (next : Fin p)
  | loadPrivate (dst addr : Fin r) (next : Fin p)
  | storePrivate (addr src : Fin r) (next : Fin p)
  | jumpEq (lhs rhs : Fin r) (yes no : Fin p)
  | jumpLt (lhs rhs : Fin r) (yes no : Fin p)
  | choose (yes no : Fin p)
  | readExternal (dst addr : Fin r) (next : Fin p)
  | writeExternal (addr src : Fin r) (next : Fin p)
  | returnState (src : Fin r)
  | accept
  | reject
  deriving DecidableEq

/-- Finite instruction table for a burst RAM call, with an entry counter and an indexed table
of public operand words. -/
structure Machine (w p r k : ℕ) where
  /-- Program counter at which every fresh call starts. -/
  entry : Fin p
  /-- Instruction fetched at each of the machine’s finite program counters. -/
  code : Fin p → Instr w p r k
  /-- Public operand words addressed by the machine’s public-word load instructions. -/
  publicData : Fin k → Word w

/-- Private RAM state within one call, consisting of its program counter, persistent input
word, registers, and addressable private memory. -/
structure Config (w p r : ℕ) where
  /-- Program counter used to fetch the next instruction. -/
  pc : Fin p
  /-- Incoming persistent state word available to state-word loads during the call. -/
  persistent : Word w
  /-- Private word stored in each of the call’s registers. -/
  reg : Fin r → Word w
  /-- Private word memory indexed by a word address and initialized to zero at call entry. -/
  privateMem : Word w → Word w

/-- Write a value to the destination register and advance to the given program counter. -/
def Config.put (c : Config w p r) (next : Fin p) (dst : Fin r) (v : Word w) : Config w p r :=
  { c with pc := next, reg := Function.update c.reg dst v }

/-- Write a word at a private-memory address and advance to the given program counter. -/
def Config.store (c : Config w p r) (next : Fin p) (addr v : Word w) : Config w p r :=
  { c with pc := next, privateMem := Function.update c.privateMem addr v }

/-- Interpret one instruction as a local step, binary choice, external memory probe, return of
a persistent word, accepting halt, or rejection. -/
def Instr.run (i : Instr w p r k) (pub : Fin k → Word w) (c : Config w p r) :
    CallAction w (Config w p r) :=
  match i with
  | .constant dst v next => .localStep (c.put next dst v)
  | .publicWord dst j next => .localStep (c.put next dst (pub j))
  | .stateWord dst next => .localStep (c.put next dst c.persistent)
  | .copy dst src next => .localStep (c.put next dst (c.reg src))
  | .binary op dst x y next => .localStep (c.put next dst (op.eval (c.reg x) (c.reg y)))
  | .loadPrivate dst addr next => .localStep (c.put next dst (c.privateMem (c.reg addr)))
  | .storePrivate addr src next => .localStep (c.store next (c.reg addr) (c.reg src))
  | .jumpEq x y yes no => .localStep {c with pc := if c.reg x = c.reg y then yes else no}
  | .jumpLt x y yes no => .localStep {c with pc := if c.reg x < c.reg y then yes else no}
  | .choose yes no => .branch fun b => {c with pc := if b then yes else no}
  | .readExternal dst addr next => .read (c.reg addr) fun v => c.put next dst v
  | .writeExternal addr src next => .write (c.reg addr) (c.reg src) {c with pc := next}
  | .returnState src => .finish (some (c.reg src))
  | .accept => .finish none
  | .reject => .reject

/-- Executable translation to the burst interpreter. Resetting the private
workspace is part of call entry in this machine model. -/
def Machine.program (M : Machine w p r k) : Program w (Config w p r) where
  start s := ⟨M.entry, s, fun _ => 0, fun _ => 0⟩
  step c := (M.code c.pc).run M.publicData c

theorem Machine.start_spec (M : Machine w p r k) (s : Word w) :
    (M.program.start s).pc = M.entry ∧ (M.program.start s).persistent = s ∧
      (∀ i, (M.program.start s).reg i = 0) ∧ (∀ a, (M.program.start s).privateMem a = 0) :=
  ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The value returned by an external read is available to every later
instruction, in particular to the address operand of another probe. -/
theorem Machine.step_read (M : Machine w p r k) (c : Config w p r)
    {dst addr : Fin r} {next : Fin p} (h : M.code c.pc = .readExternal dst addr next) :
    M.program.step c = .read (c.reg addr) (fun v => c.put next dst v) := by
  simp [Machine.program, h, Instr.run]

@[simp] theorem Config.put_same (c : Config w p r) (next : Fin p) (dst : Fin r) (v : Word w) :
    (c.put next dst v).reg dst = v := by simp [Config.put]

@[simp] theorem Config.store_same (c : Config w p r) (next : Fin p) (a v : Word w) :
    (c.store next a v).privateMem a = v := by simp [Config.store]

theorem Config.store_other (c : Config w p r) (next : Fin p) (a b v : Word w) (h : b ≠ a) :
    (c.store next a v).privateMem b = c.privateMem b := by
  simp [Config.store, Function.update_of_ne h]

/-- Two consecutive external reads can use the answer of the first as the
address of the second. This is the native execution rule on actual memory. -/
theorem Machine.execute_dependent_reads (M : Machine w p r k) (c : Config w p r)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) {dst addr dst' : Fin r} {next next' : Fin p}
    (h₁ : M.code c.pc = .readExternal dst addr next)
    (h₂ : M.code next = .readExternal dst' dst next') :
    let a := c.reg addr
    let v := mem a.val
    let u := mem v.val
    execute M.program (fuel + 2) c mem bits =
      ((execute M.program fuel ((c.put next dst v).put next' dst' u) mem bits).map
        (Report.prepend (.read v u))).map (Report.prepend (.read a v)) := by
  dsimp only
  have hs := M.step_read (c.put next dst (mem (c.reg addr).val)) h₂
  simp only [execute, M.step_read c h₁, hs, Config.put_same]

/-- A conservative word-operation accounting for a dispatch: instruction
fetch and program-counter update, operand reads, one arithmetic operation
or comparison, and a destination write. Read/write probe logging and guess
bits are counted separately. -/
def Instr.wordWork : Instr w p r k → ℕ
  | .constant .. | .stateWord .. => 3
  | .publicWord .. | .copy .. => 4
  | .binary .. => 6
  | .loadPrivate .. | .storePrivate .. | .jumpEq .. | .jumpLt .. => 5
  | .choose .. => 3
  | .readExternal .. | .writeExternal .. => 4
  | .returnState .. => 2
  | .accept | .reject => 1

theorem Instr.wordWork_le (i : Instr w p r k) : i.wordWork ≤ 6 := by
  cases i <;> simp [Instr.wordWork]

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
