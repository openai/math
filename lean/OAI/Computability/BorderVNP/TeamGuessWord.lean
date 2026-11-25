import OAI.Computability.BorderVNP.TeamGuard
import OAI.Computability.VPVNP.RAMWordBits

/-! # Guessing one previous word on the signed processor

The finite stack program makes exactly one genuine binary choice for each bit of its width
template. It restores the complete template and pushes the guessed bits onto its result stack.
The contextual counting identity holds with any signed continuation after the guess.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamGuessWord

open VPVNP.RAMTape TeamStack

/-- The word-width template, its temporary copy, and the guessed old word. -/
inductive Port | width | saved | out
  deriving DecidableEq

instance : Fintype Port := derive_fintype% Port

/-- States for guessing each bit and restoring the width template. -/
inductive State | scan | save (b : Bool) | choose | write (b : Bool) | restore | put (b : Bool) | done
  deriving DecidableEq, Fintype

/-- The guessed bits are emitted in reverse temporal order. No guess is made for padding. -/
def code : StackCode Port State
  | .scan => .pop .width fun b => b.elim .restore .save
  | .save b => .push .saved b .choose
  | .choose => .choose (.write false) (.write true)
  | .write b => .push .out b .scan
  | .restore => .pop .saved fun b => b.elim .done .put
  | .put b => .push .width b .restore
  | .done => .halt true

/-- Stack contents during a word guess. -/
def bank (width saved out : List Bool) : Stacks Port
  | .width => width
  | .saved => saved
  | .out => out

private theorem update_bank (w s out bits : List Bool) (p : Port) :
    Function.update (bank w s out) p bits = match p with
      | .width => bank bits s out | .saved => bank w bits out | .out => bank w s bits := by
  funext i; cases p <;> cases i <;> rfl

/-- Restore the width template after guessing. -/
theorem restore_run (w saved out : List Bool) :
    StackRuns code (2*saved.length+1) .restore (bank w saved out) .done (bank (saved.reverse++w) [] out) := by
  induction saved generalizing w with
  | nil =>
    refine .cons (.pop rfl) ?_
    simp only [update_bank, bank, List.head?_nil, List.tail_nil, Option.elim_none, List.reverse_nil, List.nil_append, List.length_nil, Nat.mul_zero]
    exact .nil ..
  | cons b bs ih =>
    rw [List.length_cons, show 2*(bs.length+1)+1 = ((2*bs.length+1)+1)+1 by omega]
    refine .cons (.pop rfl) (.cons (.push rfl) ?_)
    simp only [update_bank, bank, List.tail_cons,
      List.reverse_cons, List.append_assoc, List.singleton_append]
    exact ih (b :: w)

variable {K Q : Type*} [DecidableEq K]

/-- The entire physical choice tree, embedded into a larger validator. Every width-bit string
contributes the signed value of the caller's continuation exactly once. -/
theorem sum_guesses (target : StackCode K Q) (neg : Q → Bool) (ports : Port → K)
    (hp : Function.Injective ports) (labels : State → Q) (base : Stacks K)
    (rows : ∀ q, q ≠ .done → target (labels q) = (code q).rename ports labels)
    (w saved out : List Bool) (fuel : ℕ) :
    TeamStack.paths target neg (fuel + (4*w.length+1 + (2*(w.length+saved.length)+1)))
      (labels .scan) (installStacks ports base (bank w saved out)) =
    ∑ bits : Fin w.length → Bool, TeamStack.paths target neg fuel (labels .done)
      (installStacks ports base (bank (saved.reverse ++ w) [] ((List.ofFn bits).reverse ++ out))) := by
  induction w generalizing saved out with
  | nil =>
    have hre := (restore_run [] saved out).lift ports hp labels base
      (fun q h => rows q (fun e => by subst q; contradiction))
    have hscan : target (labels .scan) = (code .scan).rename ports labels := rows _ (by decide)
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.reverse_nil, List.append_nil,
      List.ofFn_zero, List.nil_append, Fintype.sum_unique]
    rw [show fuel+(1+(2*saved.length+1)) = (fuel+(2*saved.length+1))+1 by omega,
      TeamStack.paths, hscan]
    simp only [code, StackOp.rename, Function.comp_apply, installStacks_at hp, installStacks_update hp,
      bank, List.head?_nil, Option.elim_none, List.tail_nil, update_bank]
    simpa only [List.append_nil] using TeamGuard.runs_paths hre neg fuel
  | cons a w ih =>
    let t := fuel + (4*w.length+1 + (2*(w.length+(a::saved).length)+1))
    have time : fuel + (4*(a::w).length+1 + (2*((a::w).length+saved.length)+1)) = (((t+1)+1)+1)+1 := by
      dsimp [t]; omega
    rw [time]
    have hscan := rows .scan (by decide)
    have hsave := rows (.save a) (by simp)
    have hchoice := rows .choose (by decide)
    have hwrite (b : Bool) := rows (.write b) (by simp)
    simp only [TeamStack.paths, hscan, code, StackOp.rename, installStacks_at hp, installStacks_update hp,
      bank, update_bank, Function.comp_apply, List.head?_cons, List.tail_cons, Option.elim_some, hsave, hchoice, hwrite]
    change TeamStack.paths target neg t _ (installStacks ports base (bank w (a::saved) (false::out))) +
      TeamStack.paths target neg t _ (installStacks ports base (bank w (a::saved) (true::out))) = _
    rw [ih (a::saved) (false::out), ih (a::saved) (true::out)]
    simp only [List.length_cons]
    rw [← (Fin.consEquiv (fun _ : Fin (w.length+1) => Bool)).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    simp [Fin.consEquiv, List.append_assoc]

end TeamGuessWord

end BorderVNP
end Computability
end OAI
