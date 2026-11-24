import OAI.Computability.VPVNP.RAMProcessorFlow
import OAI.Computability.VPVNP.RAMTapeISADispatch
import OAI.Computability.VPVNP.RAMProcessorLogged

/-!
# Fuel-checked private instruction execution between external probes

The controller consumes an instruction credit before fetching the opcode.
Ordinary continuations jump to the next credit test. A private choice consumes
one already nominated bit, with a short stream reaching rejection. Read and
write callbacks return to the site controller for charging and recording.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.LocalProcessor

open BurstRAM PrivateRAM

variable {p r k w : ℕ}

/-- Ports of the private instruction interpreter together with its unary fuel stack and binary
guess stream. -/
abbrev Port (r k : ℕ) := ISA.Port r k ⊕ Bool

/-- Stack holding one token per remaining private instruction. -/
def fuelPort : Port r k := .inr false
/-- Stack containing the remaining nominated binary choices for private branches. -/
def choicePort : Port r k := .inr true

/-- Control states for checking fuel at a program counter, executing an ISA instruction and
yielding its callback. -/
inductive State (T : Template p r k) where
  | begin (pc : Fin p)
  | instr (q : ISA.State T)
  | exit (cb : ISA.Callback p r)
  deriving Fintype

/-- Consume one fuel token before dispatch, follow private branches using the choice stack, and
yield external actions or termination to the site controller. -/
def code (T : Template p r k) : StackCode (Port r k) (State T)
  | .begin pc => .pop fuelPort fun x => if x.isSome then .instr (ISA.entry T pc) else .exit .reject
  | .instr q => match ISA.resume? T q with
    | none => (ISA.code T q).rename Sum.inl State.instr
    | some (.next pc) => .goto (.begin pc)
    | some (.choose yes no) => .pop choicePort fun b => match b with
      | none => .exit .reject
      | some b => .begin (if b then yes else no)
    | some cb => .goto (.exit cb)
  | .exit _ => .halt true

/-- Build the local interpreter's stack bank from the public words, logged private
configuration, fuel tally and remaining guess bits. -/
def store (pub : Fin k → Word w) (c : LogConfig w p r) (fuel : ℕ) (bits : List Bool) : Stacks (Port r k) :=
  Sum.elim (ISA.configBank pub c) (fun b => if b then bits else List.replicate fuel true)

theorem putFuel (pub : Fin k → Word w) (c : LogConfig w p r) (f f' : ℕ) (bs : List Bool) :
    Function.update (store pub c f bs) fuelPort (List.replicate f' true) = store pub c f' bs := by
  funext j
  rcases j with j | b
  · simp [fuelPort, store]
  · cases b <;> simp [fuelPort, store]

theorem putChoices (pub : Fin k → Word w) (c : LogConfig w p r) (f : ℕ) (bs tail : List Bool) :
    Function.update (store pub c f bs) choicePort tail = store pub c f tail := by
  funext j
  rcases j with j | b
  · simp [choicePort, store]
  · cases b <;> simp [choicePort, store]

private theorem installed (pub : Fin k → Word w) (old new : LogConfig w p r) (fuel : ℕ) (bs : List Bool) :
    installStacks Sum.inl (store pub old fuel bs) (ISA.configBank pub new) = store pub new fuel bs := by
  funext j
  rcases j with j | b
  · exact installStacks_at Sum.inl_injective ..
  · exact installStacks_outside _ _ (by simp)

/-- Callback selected by the current template instruction and its conditional jump test on the
logged configuration. -/
def instructionExit (T : Template p r k) (c : LogConfig w p r) :=
  ISA.exitFor (T.code c.pc) ((ISA.jumpTest (T.code c.pc) c).getD false)

/-- Logged private configuration after the current instruction's register and private-memory
updates. -/
def instructionPost (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :=
  ISA.post (T.code c.pc) pub c

theorem fetch (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) (fuel : ℕ)
    (bits : List Bool) :
    ∃ ticks ≤ ISA.prepareBound w c.writes.length+3,
      StackRuns (code T) ticks (.begin c.pc) (store pub c (fuel+1) bits)
        (.instr (ISA.callback T (instructionExit T c))) (store pub (instructionPost T pub c) fuel bits) := by
  obtain ⟨t, ht, run⟩ := ISA.dispatch_step T pub c
  have lift := run.lift Sum.inl Sum.inl_injective State.instr (store pub c fuel bits)
    (target := code T) (by intro q h; simp only [code, ISA.resume_none_of_continuing T q h])
  rw [installed, installed] at lift
  have first := StackStep.pop (s := store pub c (fuel+1) bits) (code := code T) (q := .begin c.pc)
    (show code T (.begin c.pc) = .pop fuelPort _ from rfl)
  change StackStep (code T) (.begin c.pc) (store pub c (fuel+1) bits) (.instr (ISA.entry T c.pc))
    (Function.update (store pub c (fuel+1) bits) fuelPort (List.replicate fuel true)) at first
  rw [putFuel] at first
  exact ⟨_, by omega, .cons first lift⟩

theorem cutoff (T : Template p r k) (pub : Fin k → Word w) (c : LogConfig w p r) (bits : List Bool) :
    StackRuns (code T) 1 (.begin c.pc) (store pub c 0 bits) (.exit .reject) (store pub c 0 bits) := by
  have hs := StackStep.pop (s := store pub c 0 bits) (code := code T) (q := .begin c.pc)
    (show code T (.begin c.pc) = .pop fuelPort _ from rfl)
  change StackStep (code T) _ _ (.exit .reject) (Function.update _ fuelPort (List.replicate 0 true)) at hs
  rw [putFuel] at hs
  exact .cons hs (.nil ..)

theorem next_step (T : Template p r k) (pc : Fin p) (s : Stacks (Port r k)) :
    StackStep (code T) (.instr (ISA.callback T (.next pc))) s (.begin pc) s :=
  .goto (by simp [code, ISA.resume_callback])

theorem branch_step (T : Template p r k) (yes no : Fin p) (pub : Fin k → Word w)
    (c : LogConfig w p r) (f : ℕ) (b : Bool) (tail : List Bool) :
    StackStep (code T) (.instr (ISA.callback T (.choose yes no))) (store pub c f (b :: tail))
      (.begin (if b then yes else no)) (store pub c f tail) := by
  have hs := StackStep.pop (s := store pub c f (b :: tail)) (code := code T)
    (q := .instr (ISA.callback T (.choose yes no))) (show code T _ = .pop choicePort _ from rfl)
  change StackStep (code T) _ _ (.begin (if b then yes else no)) (Function.update _ choicePort tail) at hs
  rwa [putChoices] at hs

theorem short_choice (T : Template p r k) (yes no : Fin p) (pub : Fin k → Word w)
    (c : LogConfig w p r) (f : ℕ) :
    StackStep (code T) (.instr (ISA.callback T (.choose yes no))) (store pub c f [])
      (.exit .reject) (store pub c f []) := by
  have hs := StackStep.pop (s := store pub c f []) (code := code T)
    (q := .instr (ISA.callback T (.choose yes no))) (show code T _ = .pop choicePort _ from rfl)
  change StackStep (code T) _ _ (.exit .reject) (Function.update _ choicePort []) at hs
  rwa [putChoices] at hs

end RAMTape.LocalProcessor

end VPVNP
end Computability
end OAI
