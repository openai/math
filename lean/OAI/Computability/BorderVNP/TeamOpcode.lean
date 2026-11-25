import OAI.Computability.BorderVNP.TeamRAM
import OAI.Computability.BorderVNP.TeamOpcodeSelect
import OAI.Computability.VPVNP.RAMTapeISADispatch

/-! # The finite instruction table of the signed team RAM

Ordinary word instructions use the project's register arithmetic and jumps. Explicit
sign and private call opcodes extend that fixed table. A call reads the consecutive words
selected by its address and length registers. Registers and the counter persist across all
ordinary and private calls. A zero divisor and forbidden operations reject.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamOpcode

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM VPVNP.RAMTape

variable {v w p r k m : ℕ}

/-- Choose the base opcode or one of the two additional kinds of signed team instruction. -/
inductive Tag (p r m : ℕ) where
  | native
  | sign (negative : Bool) (next : Fin p)
  | call (routine : Fin m) (address length : Fin r) (next : Fin p)
  | callReg (routineID address length : Fin r) (next : Fin p)
  deriving DecidableEq

/-- One fixed table, whose literals can be installed at any runtime width. -/
structure Program (p r k m : ℕ) where
  /-- Finite register, arithmetic, conditional, and external probe table. -/
  base : Template p r k
  /-- Signed instructions and read-only private macro calls. -/
  tag : Fin p → Tag p r m

/-- Control and the finite register bank at an instruction boundary. -/
structure State (w p r : ℕ) where
  /-- Instruction counter. -/
  pc : Fin p
  /-- Words carried across instructions and handoffs. -/
  reg : Fin r → Word w

/-- Lift the registers into the existing physical arithmetic dispatcher, with no private log. -/
def State.logged (s : State w p r) : LogConfig w p r := ⟨s.pc, 0, s.reg, []⟩

/-- Register actions dispatched without involving hidden private memory or a return stack. -/
def permitted : Instr v p r k → Bool
  | .loadPrivate .. | .storePrivate .. | .returnState .. => false
  | _ => true

/-- Register requiring a nonzero operand for Euclidean division. -/
def divisor : Instr v p r k → Option (Fin r)
  | .binary .div _ _ y _ | .binary .mod _ _ y _ => some y
  | _ => none

/-- The admissibility check uses the original bank before a binary opcode can overwrite its
own divisor. -/
def enabled (i : Instr v p r k) (s : State w p r) : Bool :=
  permitted i && (divisor i).all fun y => decide (s.reg y ≠ 0)

/-- Translate a decoded ordinary action to the local/shared instructions of §7.2. -/
def nativeAction : CallAction w (LogConfig w p r) → TeamRAM.Instr w (State w p r)
  | .localStep s => .localStep ⟨s.pc, s.reg⟩ .plus
  | .branch f => .choose fun b => ⟨(f b).pc, (f b).reg⟩
  | .read a f => .load a fun v => ⟨(f v).pc, (f v).reg⟩
  | .write a v s => .store a v ⟨s.pc, s.reg⟩
  | .finish none => .accept
  | .finish (some _) | .reject => .reject

/-- The signed private macros have exactly the private word input and choice list in the
manuscript's local call semantics. -/
abbrev Macros (w m : ℕ) := Fin m → List (Word w) → List Bool → Option TeamRAM.Sign

/-- The decoded finite table operating on actual persistent register values. -/
def Program.fetch (P : Program p r k m) (pub : Fin k → Word w) (macros : Macros w m)
    (s : State w p r) : TeamRAM.Instr w (State w p r) :=
  match P.tag s.pc with
  | .native => let i := P.base.code s.pc
               if enabled i s then nativeAction ((i.resize w).runLogged pub s.logged) else .reject
  | .sign minus next => .localStep { s with pc := next } (if minus then .minus else .plus)
  | .call j a l next => .call (s.reg a) (s.reg l).val (macros j) {s with pc := next}
  | .callReg idReg a l next =>
    match TeamOpcodeSelect.select m (s.reg idReg).val with
    | some j => .call (s.reg a) (s.reg l).val (macros j) {s with pc := next}
    | none => .reject

/-- A typed exit tells the enclosing processor which continuation and old-word probes to run. -/
inductive Exit (p r m : ℕ) where
  | native (action : ISA.Callback p r)
  | sign (negative : Bool) (next : Fin p)
  | call (routine : Fin m) (address length : Fin r) (next : Fin p)
  deriving DecidableEq, Fintype

/-- A dynamically selected subroutine reaches the same typed callback as a literal
routine number. An invalid identifier rejects before any private choice or probe. -/
def selectedExit (id : Option (Fin m)) (address length : Fin r) (next : Fin p) : Exit p r m :=
  id.elim (.native .reject) (fun j => .call j address length next)

/-- The semantics of the physical exit after arithmetic register preparation. -/
def Exit.action (macros : Macros w m) (s : LogConfig w p r) : Exit p r m → TeamRAM.Instr w (State w p r)
  | .native cb => nativeAction (cb.action s)
  | .sign b next => .localStep ⟨next, s.reg⟩ (if b then .minus else .plus)
  | .call j a l next => .call (s.reg a) (s.reg l).val (macros j) ⟨next, s.reg⟩

/-- The typed exit and the bank prepared before the external word or choice is obtained. -/
def prepare (P : Program p r k m) (pub : Fin k → Word w) (s : State w p r) : Exit p r m × LogConfig w p r :=
  match P.tag s.pc with
  | .native => let i := P.base.code s.pc
               if enabled i s then
                 (.native (ISA.exitFor i ((ISA.jumpTest i s.logged).getD false)), ISA.post i pub s.logged)
               else (.native .reject, s.logged)
  | .sign b next => (.sign b next, s.logged)
  | .call j a l next => (.call j a l next, s.logged)
  | .callReg idReg a l next => (selectedExit (TeamOpcodeSelect.select m (s.reg idReg).val) a l next,s.logged)

/-- The word-level dispatcher obtains precisely the next adaptive instruction, with no
prior access to the unknown word returned by a shared-memory load. -/
theorem prepare_action (P : Program p r k m) (pub : Fin k → Word w) (s : State w p r) (macros : Macros w m) :
    (prepare P pub s).1.action macros (prepare P pub s).2 = P.fetch pub macros s := by
  cases h : P.tag s.pc with
  | native =>
    by_cases he : enabled (P.base.code s.pc) s = true
    · simp only [prepare, Program.fetch, h, he, ↓reduceIte, Exit.action, ISA.callback_action]
    · simp [prepare, Program.fetch, h, he, Exit.action, nativeAction, ISA.Callback.action]
  | sign b j => simp [prepare, Program.fetch, h, Exit.action, State.logged]
  | call j a l q => simp [prepare, Program.fetch, h, Exit.action, State.logged]

  | callReg idReg a l next =>
    cases hs : TeamOpcodeSelect.select m (s.reg idReg).val <;>
      simp [prepare,Program.fetch,h,hs,selectedExit,Exit.action,nativeAction,ISA.Callback.action,State.logged]

end TeamOpcode

end BorderVNP
end Computability
end OAI
