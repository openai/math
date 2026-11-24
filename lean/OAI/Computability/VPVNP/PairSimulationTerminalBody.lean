import OAI.Computability.VPVNP.PairSimulationTerminalLink

/-!
# Exact finite-fuel semantics inside a terminal worker

The protected registers hold the restored worker state, its two header
addresses and the marker one. Ordinary instructions simulate one source
instruction each. On a continuing exit the controller records the next
worker and its entire word. Every insufficient fuel or unused choice
stream is accounted for by the same interpreter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalLink

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {r w : ℕ} {pcs : Stage → ℕ}

/-- The worker and persistent word selected by a successful exit. -/
def target (s : Stage) : Option (Word w) → Option (Stage × Word w)
  | some v => some (s,v)
  | none => (next s).map (fun t => (t,0))

/-- Instructions that publish the next stage and its persistent word. -/
def exitEvents (addr : Word w) (s : Stage) (v : Word w) : List (Event w) :=
  [.tick,.tick,.write addr (tagWord w s),.write (addr+31) v]

/-- Extend the worker's report by the control writes at a continuing exit. -/
def exitReport (addr : Word w) (s : Stage) (rep : Report w) : Report w :=
  match target s rep.result with
  | none => rep
  | some (t,v) => ⟨rep.events++exitEvents addr t v, some 1⟩

/-- Check that the worker and its control writes fit in the remaining fuel. -/
def boundedExit (addr : Word w) (s : Stage) (f : ℕ) (rep : Report w) : Option (Report w) :=
  let out := exitReport addr s rep
  if out.events.length < f then some out else none

theorem exitReport_prepend (addr : Word w) (s : Stage) (rep : Report w) (e : Event w) :
    exitReport addr s (rep.prepend e) = (exitReport addr s rep).prepend e := by
  unfold exitReport Report.prepend
  cases h : target s rep.result <;> rfl

private theorem bind_prepend (addr : Word w) (s : Stage) (f : ℕ) (ev : Event w) (rep : Option (Report w)) :
    (rep.bind (boundedExit addr s f)).map (Report.prepend ev) =
      (rep.map (Report.prepend ev)).bind (boundedExit addr s (f+1)) := by
  cases rep with
  | none => rfl
  | some x =>
    simp only [Option.bind_some,Option.map_some,boundedExit]
    rw [exitReport_prepend]
    simp only [Report.prepend,List.length_cons,Nat.add_lt_add_iff_right]
    split <;> rfl

private theorem update_ordinary (small : Fin r → Word w) (tail : Fin 6 → Word w) (j : Fin r) (v : Word w) :
    Function.update (Fin.append small tail) (ordinary j) v = Fin.append (Function.update small j v) tail := by
  funext i
  cases i using Fin.addCases with
  | left i => by_cases h : i = j <;> simp [ordinary,Function.update,h]
  | right i =>
    have ne : i.natAdd r ≠ j.castAdd 6 := by intro e; have := congrArg Fin.val e; simp at this; omega
    simp [ordinary,Function.update,ne]

private def mapAction {A B : Type} (g : A → B) : CallAction w A → CallAction w B
  | .localStep c => .localStep (g c)
  | .branch f => .branch (g ∘ f)
  | .read a f => .read a (g ∘ f)
  | .write a v c => .write a v (g c)
  | .reject => .reject
  | .finish x => .finish x

private def terminal {p : ℕ} : Instr w p r 11 → Bool
  | .returnState _ | .accept => true
  | _ => false

variable (T : (s : Stage) → Template (pcs s) r 11) (pub : Fin 11 → Word w)

private theorem body_step (s : Stage) (host addr tag tmp : Word w) (c : Config w (pcs s) r)
    (h : terminal (((T s).instantiate w pub).code c.pc) = false) :
    (machine T pub).program.step (bodyConfig s host addr tag tmp c) =
      mapAction (bodyConfig s host addr tag tmp) (((T s).instantiate w pub).program.step c) := by
  change ((machine T pub).code (bodyPC pcs s c.pc)).run pub _ = _
  rw [code_body]
  change (bodyInstr s _).run pub _ = mapAction _ ((((T s).instantiate w pub).code c.pc).run pub c)
  generalize he : ((T s).instantiate w pub).code c.pc = op at h ⊢
  cases op <;> simp only [terminal, Bool.true_eq_false,bodyInstr,mapAction,Instr.run,bodyConfig,
    Config.put,Config.store,Function.comp_def,Fin.append_left,Fin.append_right,update_ordinary] at *
  all_goals first | contradiction | rfl | (split <;> rfl) | (congr 1; funext b; cases b <;> rfl)

private theorem body_return (s : Stage) (host addr tag tmp : Word w) (c : Config w (pcs s) r)
    (a : Fin r) (h : ((T s).instantiate w pub).code c.pc = .returnState a) (fuel : ℕ)
    (m : Memory w) (bits : List Bool) :
    execute (machine T pub).program fuel (bodyConfig s host addr tag tmp c) m bits =
      (execute ((T s).instantiate w pub).program fuel c m bits).bind (boundedExit addr s fuel) := by
  rcases fuel with _|_|_|_|_|f <;> cases bits <;>
    simp [execute,Machine.program,code_body,h,bodyInstr,Instr.run,bodyConfig,Config.put,
      ordinary,extras,phaseAddress,savedAddress,stateValue,phaseValue,unitReg,extra,saveInstr,
      boundedExit,exitReport,target,exitEvents,Report.prepend]

private theorem body_accept (s : Stage) (host addr tag tmp : Word w) (c : Config w (pcs s) r)
    (h : ((T s).instantiate w pub).code c.pc = .accept) (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (machine T pub).program fuel (bodyConfig s host addr tag tmp c) m bits =
      (execute ((T s).instantiate w pub).program fuel c m bits).bind (boundedExit addr s fuel) := by
  cases n : next s with
  | none =>
    cases fuel <;> cases bits <;> simp [execute,Machine.program,code_body,h,bodyInstr,n,Instr.run,
      bodyConfig,boundedExit,exitReport,target]
  | some dst =>
    rcases fuel with _|_|_|_|_|f <;> cases bits <;>
      simp [execute,Machine.program,code_body,h,bodyInstr,n,Instr.run,bodyConfig,Config.put,
        extras,phaseAddress,savedAddress,stateValue,phaseValue,unitReg,extra,saveInstr,
        boundedExit,exitReport,target,exitEvents,Report.prepend]

/-- Exact success and failure of a worker with the real exit protocol.
This equality is valid for all fuel, registers, private memory, external
memory and binary streams. -/
theorem execute_body (s : Stage) (host addr tag tmp : Word w) (fuel : ℕ) (c : Config w (pcs s) r)
    (m : Memory w) (bits : List Bool) :
    execute (machine T pub).program fuel (bodyConfig s host addr tag tmp c) m bits =
      (execute ((T s).instantiate w pub).program fuel c m bits).bind (boundedExit addr s fuel) := by
  induction fuel generalizing c m bits with
  | zero => rfl
  | succ fuel ih =>
    by_cases last : terminal (((T s).instantiate w pub).code c.pc) = true
    · cases he : ((T s).instantiate w pub).code c.pc with
      | accept => exact body_accept T pub s host addr tag tmp c he _ m bits
      | returnState a => exact body_return T pub s host addr tag tmp c a he _ m bits
      | _ => simp [he,terminal] at last
    · rw [execute,body_step T pub s host addr tag tmp c (Bool.eq_false_iff.mpr last),execute]
      cases hs : ((T s).instantiate w pub).program.step c with
      | localStep x => simp only [mapAction,ih]; exact bind_prepend ..
      | branch f =>
        cases bits <;> simp only [mapAction,Function.comp_apply,ih,Option.bind_none]
        exact bind_prepend ..
      | read a f => simp only [mapAction,Function.comp_apply,ih]; exact bind_prepend ..
      | write a v x => simp only [mapAction,ih]; exact bind_prepend ..
      | reject => rfl
      | finish z =>
        change ((((T s).instantiate w pub).code c.pc).run pub c) = _ at hs
        cases he : ((T s).instantiate w pub).code c.pc <;> simp_all [terminal,Instr.run]

end PairSimulation.TerminalLink

end VPVNP
end Computability
end OAI
