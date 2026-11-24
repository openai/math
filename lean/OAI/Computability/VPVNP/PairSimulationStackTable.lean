import OAI.Computability.VPVNP.RAMTapeStacks
import OAI.Computability.VPVNP.PrimedCounterGuessWord
import Mathlib.Tactic.DeriveFintype

/-!
# Finite private RAM table for a named bit-stack program

Each continuing stack instruction uses exactly four native transitions.
Stack top and base pointers are retained in separate registers. No opcode
accesses external memory. The true halt jumps to the caller's continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape BurstRAM BurstRAM.PrivateRAM

/-- Logical registers of the bit-stack machine, with a base and exclusive top pointer per stack
and shared zero, one, and temporary registers. -/
inductive Register (K : Type) where
  | top (k : K)
  | base (k : K)
  | zero
  | one
  | tmp
  deriving DecidableEq, Fintype

variable {K Q : Type} {w p r k : ℕ}

/-- Unused instruction slots reject. Empty and nonempty pops have separate
three-transition continuations after the initial pointer comparison. -/
def instruction (code : StackCode K Q) (pc : Q → Fin 7 → Fin p)
    (reg : Register K ↪ Fin r) (done : Fin p) (q : Q) (i : Fin 7) : Instr w p r k :=
  let pass (dst : Fin p) : Instr w p r k := .copy (reg .tmp) (reg .tmp) dst
  match code q with
  | .push a b next => ![.constant (reg .tmp) (if b then 1 else 0) (pc q 1),
      .storePrivate (reg (.top a)) (reg .tmp) (pc q 2),
      .binary .add (reg (.top a)) (reg (.top a)) (reg .one) (pc q 3),
      pass (pc next 0), .reject, .reject, .reject] i
  | .pop a next => ![.jumpEq (reg (.top a)) (reg (.base a)) (pc q 4) (pc q 1),
      .binary .sub (reg (.top a)) (reg (.top a)) (reg .one) (pc q 2),
      .loadPrivate (reg .tmp) (reg (.top a)) (pc q 3),
      .jumpEq (reg .tmp) (reg .zero) (pc (next (some false)) 0) (pc (next (some true)) 0),
      pass (pc q 5),pass (pc q 6),pass (pc (next none) 0)] i
  | .goto next => ![pass (pc q 1),pass (pc q 2),pass (pc q 3),pass (pc next 0),.reject,.reject,.reject] i
  | .choose lo hi => ![pass (pc q 1),pass (pc q 2),pass (pc q 3),.choose (pc hi 0) (pc lo 0),.reject,.reject,.reject] i
  | .halt b => if b && i == 0 then pass done else .reject

/-- The host instruction table implements all seven slots for every stack-code state with the
specified register allocation and accepting continuation. -/
def Linked (M : Machine w p r k) (code : StackCode K Q) (pc : Q → Fin 7 → Fin p)
    (reg : Register K ↪ Fin r) (done : Fin p) : Prop :=
  ∀ q i, M.code (pc q i) = instruction code pc reg done q i

theorem resize_instruction (code : StackCode K Q) (pc : Q → Fin 7 → Fin p)
    (reg : Register K ↪ Fin r) (done : Fin p) (q : Q) (i : Fin 7) :
    (instruction (w := 1) (k := k) code pc reg done q i).resize w = instruction code pc reg done q i := by
  cases h : code q with
  | push a b n =>
    cases b <;> fin_cases i <;> simp [instruction,h,Instr.resize]
    rfl
  | pop | goto | choose => fin_cases i <;> simp [instruction,h,Instr.resize]
  | halt b => cases b <;> fin_cases i <;> simp [instruction,h,Instr.resize]

theorem Linked.step {M : Machine w p r k} {code : StackCode K Q} {pc : Q → Fin 7 → Fin p}
    {reg : Register K ↪ Fin r} {done : Fin p} (hl : Linked M code pc reg done)
    (c : Config w p r) (q : Q) (i : Fin 7) (hc : c.pc = pc q i) :
    M.program.step c = (instruction code pc reg done q i).run M.publicData c := by
  simp [Machine.program,hc,hl q i]

section Standalone

variable [Fintype Q] [Fintype K]

/-- Standalone stack program addresses, consisting of seven instruction slots for each control
state and one accepting exit. -/
abbrev PC (Q : Type) := (Q × Fin 7) ⊕ Unit

/-- Numbered machine program counter for instruction slot `i` in the compiled row of stack-code
state `q`. -/
noncomputable def rowPC (q : Q) (i : Fin 7) : Fin (Fintype.card (PC Q)) :=
  Fintype.equivFin (PC Q) (.inl (q,i))

/-- Numbered accepting continuation of the standalone stack program. -/
noncomputable def donePC (Q : Type) [Fintype Q] : Fin (Fintype.card (PC Q)) :=
  Fintype.equivFin (PC Q) (.inr ())

/-- Embed the named stack registers in the standalone machine's consecutively numbered register
file. -/
noncomputable def register (K : Type) [Fintype K] : Register K ↪ Fin (Fintype.card (Register K)) :=
  (Fintype.equivFin _).toEmbedding

/-- A finite complete table, before instantiating its word width. -/
noncomputable def table (code : StackCode K Q) (start : Q) :
    Template (Fintype.card (PC Q)) (Fintype.card (Register K)) 0 where
  literalWidth := 1
  entry := rowPC start 0
  code i := match (Fintype.equivFin (PC Q)).symm i with
    | .inl (q,j) => instruction code rowPC (register K) (donePC Q) q j
    | .inr _ => .accept

theorem table_linked (code : StackCode K Q) (start : Q) (pub : Fin 0 → Word w) :
    Linked ((table code start).instantiate w pub) code rowPC (register K) (donePC Q) := by
  intro q i
  simpa [Template.instantiate,table,rowPC] using resize_instruction (w := w) (k := 0)
    code rowPC (register K) (donePC Q) q i

theorem table_done (code : StackCode K Q) (start : Q) (pub : Fin 0 → Word w) :
    ((table code start).instantiate w pub).code (donePC Q) = .accept := by
  simp [Template.instantiate,table,donePC,Instr.resize]

end Standalone
end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
