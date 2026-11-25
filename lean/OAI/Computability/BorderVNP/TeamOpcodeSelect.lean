import OAI.Computability.BorderVNP.TeamLocalClockPC
import OAI.Computability.VPVNP.RAMTapeISAPorts

/-! # Selecting a private routine by its live register word

The finite routine table has one label per routine. Its selector scans the
logical word in the named register and rejects indices outside that table. The
input register and both scratch stacks are restored before returning a label.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamOpcodeSelect

open VPVNP BurstRAM RAMTape

variable {r k w a : ℕ}

/-- A word names a routine exactly when its unsigned value is in the fixed library. -/
def select (a n : ℕ) : Option (Fin a) := if h : n < a then some ⟨n,h⟩ else none

/-- The selected routine has exactly the register's unsigned index. -/
@[simp] theorem select_some_iff (a n : ℕ) (j : Fin a) : select a n = some j ↔ n = j.val := by
  by_cases h : n < a
  · simp [select,h,Fin.ext_iff]
  · have ne : n ≠ j.val := fun eq => h (eq ▸ j.isLt)
    simp [select,h,ne]

/-- Indices outside the fixed table always return the rejecting continuation. -/
@[simp] theorem select_none_iff (a n : ℕ) : select a n = none ↔ a ≤ n := by
  by_cases h : n < a <;> simp [select,h,not_le.mpr,not_lt.mp]

private def routine : TeamLocalClockPC.Outcome a → Option (Fin a)
  | .live j => some j
  | .accepted | .reject => none

private theorem routine_lookup (a n : ℕ) : routine (TeamLocalClockPC.lookup a n) = select a n := by
  let clipped := select a n
  change routine (match clipped with | none => .reject | some j => .live j) = clipped
  cases clipped <;> rfl

/-- Selector entry, the finite index decoder, and the possibly missing routine label. -/
inductive State (a : ℕ) where
  | enter
  | scan (q : TeamLocalClockPC.State a)
  | done (j : Option (Fin a))
  deriving Fintype

/-- The temporary live-status bit and reversal scratch use separate ISA work
ports. The decoded word is the opcode's designated live RAM register. -/
def ports (idReg : Fin r) : TeamLocalClockPC.Port → ISA.Port r k
  | .tag => .work 14
  | .pc => .reg idReg
  | .tmp => .work 15

theorem ports_injective (idReg : Fin r) : Function.Injective (ports (k := k) idReg) := by
  intro i j h; cases i <;> cases j <;> simp_all [ports, show (14 : Fin 16) ≠ 15 by decide, show (15 : Fin 16) ≠ 14 by decide]

/-- Push a live-status bit, decode the complete word, then pop just that status
bit before continuing. The library size and register label are fixed in the code. -/
def code (a : ℕ) (idReg : Fin r) : StackCode (ISA.Port r k) (State a)
  | .enter => .push (.work 14) false (.scan .status)
  | .scan (.done out) => .pop (.work 14) (fun _ => .done (routine out))
  | .scan q => (TeamLocalClockPC.code a q).rename (ports idReg) State.scan
  | .done j => .halt j.isSome

/-- The real finite selector takes four stack operations per bit and six fixed
operations. An empty library and a zero-width word obey the same bound. The
original contents of the tag scratch and every architectural port are restored. -/
theorem run (a : ℕ) (idReg : Fin r) (bank : Stacks (ISA.Port r k)) (idWord : Word w)
    (register : bank (.reg idReg) = wordBits idWord) (scratch : bank (.work 15) = []) :
    StackRuns (code a idReg) (4*w+6) .enter bank (.done (select a idWord.val)) bank := by
  let s := Function.update bank (.work 14) (false :: bank (.work 14))
  have first : StackRuns (code a idReg) 1 .enter bank (.scan .status) s :=
    .cons (.push rfl) (.nil ..)
  have tag : s (ports idReg .tag) = false :: bank (.work 14) := Function.update_self ..
  have ne : (ISA.Port.work 15 : ISA.Port r k) ≠ .work 14 := fun he =>
    (by decide : (15 : Fin 16) ≠ 14) (ISA.Port.work.inj he)
  have tmp : s (ports idReg .tmp) = [] := (Function.update_of_ne ne ..).trans scratch
  have word : s (ports idReg .pc) = wordBits idWord :=
    (Function.update_of_ne (by simp : (ISA.Port.reg idReg : ISA.Port r k) ≠ .work 14) ..).trans register
  have inner := TeamLocalClockPC.live_run a (s ∘ ports idReg) (bank (.work 14)) tag tmp
  have lifted := inner.lift (ports idReg) (ports_injective idReg) State.scan s (target := code a idReg) (by
    intro q h
    cases q with
    | done out => cases out <;> contradiction
    | _ => rfl)
  rw [installStacks_eq (ports_injective idReg) s (s ∘ ports idReg) (fun _ => rfl)] at lifted
  simp only [Function.comp_apply,word,length_wordBits,TapeWord.value_wordBits] at lifted
  let out := TeamLocalClockPC.lookup a idWord.val
  have endStep := StackStep.pop (k := ISA.Port.work 14) (s := s)
    (f := fun _ => State.done (routine out)) (q := State.scan (.done out)) (code := code a idReg) rfl
  have done : Function.update s (.work 14) (s (.work 14)).tail = bank := by
    change Function.update s (.work 14) (s (ports idReg .tag)).tail = bank
    rw [tag,List.tail_cons,Function.update_idem,Function.update_eq_self]
  rw [done] at endStep
  have last : StackRuns (code a idReg) 1 (.scan (.done out)) s (.done (select a idWord.val)) bank := by
    rw [← routine_lookup]
    exact .cons endStep (.nil ..)
  simpa only [show 1+(4*w+4)+1 = 4*w+6 by omega] using (first.trans lifted).trans last

/-- The selector embedded at arbitrary caller labels returns the dynamic routine
identifier on the original ISA bank. The caller chooses the actions for both
an out-of-range index and a valid routine. -/
theorem run_linked {Z : Type} (a : ℕ) (idReg : Fin r) (bank : Stacks (ISA.Port r k))
    (idWord : Word w) (register : bank (.reg idReg) = wordBits idWord) (scratch : bank (.work 15) = [])
    (target : StackCode (ISA.Port r k) Z) (label : State a → Z)
    (rows : ∀ q, ((code (k := k) a idReg) q).returns = false →
      target (label q) = ((code a idReg) q).rename id label) :
    StackRuns target (4*w+6) (label .enter) bank (label (.done (select a idWord.val))) bank := by
  have h := (run a idReg bank idWord register scratch).lift id Function.injective_id label bank rows
  have eq : installStacks id bank bank = bank := funext (installStacks_at Function.injective_id bank bank)
  simpa only [eq] using h

end TeamOpcodeSelect

end BorderVNP
end Computability
end OAI
