import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine
import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Compile a scalar-oracle program to an ordinary relocatable RAM fragment.
Source code operates in the odd bank and real query callbacks run at their own
physical program counters. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace OracleInline

open RAM RAM.Callable Contract

abbrev Handler := Nat → Nat → Nat → Nat → Fragment

def fallsThrough : Instr → Bool
  | .branchLT .. | .branchAddrLT .. | .jump _ | .halt _ => false
  | _ => true

def coreWidth : Instr → Nat
  | .branchLT .. | .branchAddrLT .. | .jump _ | .halt _ => 1
  | i => (Odd.instr i).size

def width (handler : Handler) : OracleInstr → Nat
  | .core i => coreWidth i
  | .query src len dst count => (handler src len dst count).size

/-- Every source halt returns to the fragment's continuation. Scalar and address
branches test translated odd registers and jump to expanded source locations. -/
def coreCode (addr : Nat → Nat) (stop here : Nat) : Instr → Program
  | .branchLT a b yes no => [(Odd.cond (.scalarLT a b)).instr (addr yes) (addr no)]
  | .branchAddrLT a b yes no => [(Odd.cond (.addrLT a b)).instr (addr yes) (addr no)]
  | .jump target => [.jump (addr target)]
  | .halt _ => [.jump stop]
  | i => (Odd.instr i).compile here

def instruction (handler : Handler) (addr : Nat → Nat) (stop here : Nat) : OracleInstr → Program
  | .core i => coreCode addr stop here i
  | .query src len dst count => (handler src len dst count).emit here

theorem coreCode_fallsThrough (i : Instr) (h : fallsThrough i = true) (addr : Nat → Nat) (stop here : Nat) :
    coreCode addr stop here i = (Odd.instr i).compile here := by
  cases i <;> first | rfl | contradiction

theorem coreWidth_fallsThrough (i : Instr) (h : fallsThrough i = true) :
    coreWidth i = (Odd.instr i).size := by
  cases i <;> first | rfl | contradiction

theorem coreWidth_le_four (i : Instr) : coreWidth i ≤ 4 := by
  cases i <;> first | exact (by decide : 1 ≤ 4) | exact (by decide : 2 ≤ 4) | exact le_rfl

theorem coreWidth_eq_instrCost (i : Instr) (h : fallsThrough i = true) : coreWidth i = Odd.instrCost i := by
  rw [coreWidth_fallsThrough i h]
  cases i <;> rfl

theorem coreCode_length (addr : Nat → Nat) (stop here : Nat) (i : Instr) :
    (coreCode addr stop here i).length = coreWidth i := by
  cases i <;> rfl

theorem instruction_length (handler : Handler) (addr : Nat → Nat) (stop here : Nat) (op : OracleInstr) :
    (instruction handler addr stop here op).length = width handler op := by
  cases op with
  | core i => exact coreCode_length addr stop here i
  | query src len dst count => exact (handler src len dst count).length_emit here

/-- Physical location of a source program counter, including the one-past-end PC. -/
def entry (source : OracleProgram) (handler : Handler) (base pc : Nat) : Nat :=
  base+((source.take pc).map (width handler)).sum

@[simp] theorem entry_start (source : OracleProgram) (handler : Handler) (base : Nat) :
    entry source handler base 0=base := by simp [entry]

theorem entry_succ {source : OracleProgram} {handler : Handler} {base pc : Nat} {op : OracleInstr}
    (fetch : source[pc]?=some op) :
    entry source handler base (pc+1)=entry source handler base pc+width handler op := by
  obtain ⟨hpc,rfl⟩ := List.getElem?_eq_some_iff.mp fetch
  unfold entry
  rw [List.take_succ_eq_append_getElem hpc]
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.add_zero,Nat.add_assoc]

private def assemble (handler : Handler) (addr : Nat → Nat) (stop : Nat) : Nat → OracleProgram → Program
  | _, [] => []
  | here, op::tail => instruction handler addr stop here op ++
      assemble handler addr stop (here+width handler op) tail

private theorem assemble_length (handler : Handler) (addr : Nat → Nat) (stop here : Nat) (source : OracleProgram) :
    (assemble handler addr stop here source).length = (source.map (width handler)).sum := by
  induction source generalizing here with
  | nil => rfl
  | cons op tail ih => simp [assemble,instruction_length,ih]

/-- Install each query fragment at its actual physical PC, retaining absolute jumps
inside it and the callback's fallthrough to the next source instruction. -/
def fragment (source : OracleProgram) (handler : Handler) : Fragment where
  size := (source.map (width handler)).sum
  emit base := assemble handler (entry source handler base) (entry source handler base source.length) base source
  length_emit base := assemble_length handler _ _ base source

@[simp] theorem entry_end (source : OracleProgram) (handler : Handler) (base : Nat) :
    entry source handler base source.length = base+(fragment source handler).size := by simp [entry,fragment]

private theorem at_assemble {target : Program} (handler : Handler) (addr : Nat → Nat) (stop : Nat)
    (source : OracleProgram) (here pc : Nat) (op : OracleInstr)
    (code : CodeAt target here (assemble handler addr stop here source)) (fetch : source[pc]? = some op) :
    CodeAt target (entry source handler here pc) (instruction handler addr stop (entry source handler here pc) op) := by
  induction source generalizing here pc with
  | nil => simp at fetch
  | cons head tail ih =>
    change CodeAt target here (instruction handler addr stop here head ++
      assemble handler addr stop (here+width handler head) tail) at code
    cases pc with
    | zero =>
      have h : head=op := by simpa using fetch
      subst op
      simpa using code.left
    | succ pc =>
      have rest := code.right
      rw [instruction_length] at rest
      have inside := ih (here+width handler head) pc rest (by simpa using fetch)
      simpa [entry,Nat.add_assoc] using inside

/-- A source fetch locates its entire installed block inside an arbitrary ordinary
RAM caller, including query callbacks of arbitrary static length. -/
theorem at_instruction {source : OracleProgram} {handler : Handler} {target : Program} {base pc : Nat}
    {op : OracleInstr} (code : CodeAt target base ((fragment source handler).emit base))
    (fetch : source[pc]?=some op) :
    CodeAt target (entry source handler base pc) (instruction handler (entry source handler base)
      (entry source handler base source.length) (entry source handler base pc) op) :=
  at_assemble handler _ _ source base pc op code fetch

theorem at_core {source : OracleProgram} {handler : Handler} {target : Program} {base pc : Nat} {i : Instr}
    (code : CodeAt target base ((fragment source handler).emit base)) (fetch : source[pc]?=some (.core i)) :
    CodeAt target (entry source handler base pc) (coreCode (entry source handler base)
      (entry source handler base source.length) (entry source handler base pc) i) :=
  at_instruction code fetch

theorem at_query {source : OracleProgram} {handler : Handler} {target : Program}
    {base pc src len dst count : Nat} (code : CodeAt target base ((fragment source handler).emit base))
    (fetch : source[pc]?=some (.query src len dst count)) :
    CodeAt target (entry source handler base pc) ((handler src len dst count).emit (entry source handler base pc)) :=
  at_instruction code fetch


private theorem assemble_map_words {α : Type*} (handler : Handler) (f : Instr → α)
    (words : OracleInstr → List α)
    (stable : ∀ addr stop here op,(instruction handler addr stop here op).map f=words op)
    (addr : Nat → Nat) (stop here : Nat) (source : OracleProgram) :
    (assemble handler addr stop here source).map f=source.flatMap words := by
  induction source generalizing here with
  | nil => rfl
  | cons op tail ih => simp [assemble,stable,ih]

/-- A position-independent observation of each installed block concatenates
exactly once per source instruction, regardless of the fragment's placement. -/
theorem fragment_map {α : Type*} (source : OracleProgram) (handler : Handler) (f : Instr → α)
    (words : OracleInstr → List α)
    (stable : ∀ addr stop here op,(instruction handler addr stop here op).map f=words op) (base : Nat) :
    ((fragment source handler).emit base).map f=source.flatMap words :=
  assemble_map_words handler f words stable _ _ base source

end OracleInline
end Recovery
end LinearProgramming
end Optimization
end OAI
