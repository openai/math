import OAI.Computability.VPVNP.RAMTapeISAPorts

/-!
# Taking one external read guess on bit stacks

The template word determines the number of bits to take from the private
choice stream. The reader restores that template and writes the guessed word
in its original order. Exhausting the stream early reaches a rejecting row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProbeWord

/-- Stacks holding the width template, choice stream, output value, saved template bits and
collected guess bits of the read-guess routine. -/
inductive Port | template | stream | value | saved | bits
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control states for clearing an old value, pairing each template bit with a guessed bit,
restoring the template and emitting the guessed word. -/
inductive State
  | clear | scan | read (widthBit : Bool) | save (widthBit guess : Bool) | collect (guess : Bool)
  | restore | putWidth (b : Bool) | output | putBit (b : Bool) | done | reject
  deriving DecidableEq, Fintype

/-- Stack instruction table that consumes one choice per template bit, restores the template
and writes the guess in its original order. A short choice stream reaches the rejecting
row. -/
def code : StackCode Port State
  | .clear => .pop .value fun b => if b.isSome then .clear else .scan
  | .scan => .pop .template fun b => b.elim .restore .read
  | .read w => .pop .stream fun b => b.elim .reject (.save w)
  | .save w b => .push .saved w (.collect b)
  | .collect b => .push .bits b .scan
  | .restore => .pop .saved fun b => b.elim .output .putWidth
  | .putWidth b => .push .template b .restore
  | .output => .pop .bits fun b => b.elim .done .putBit
  | .putBit b => .push .value b .output
  | .done => .halt true
  | .reject => .halt false

/-- Place the template word, choice stream, current value and the two partially collected bit
lists on their respective reader ports. -/
def bank (w bs val saved collected : List Bool) : Stacks Port
  | .template => w
  | .stream => bs
  | .value => val
  | .saved => saved
  | .bits => collected

private theorem at_port (w bs val saved collected new : List Bool) (i : Port) :
    Function.update (bank w bs val saved collected) i new =
      match i with
      | .template => bank new bs val saved collected
      | .stream => bank w new val saved collected
      | .value => bank w bs new saved collected
      | .saved => bank w bs val new collected
      | .bits => bank w bs val saved new := by
  funext j
  cases i <;> cases j <;> rfl

local macro "stepPop" : tactic => `(tactic|
  refine StackRuns.cons (StackStep.pop (show code _ = .pop _ _ from rfl)) ?_ <;>
    simp only [at_port, bank, List.head?_nil, List.head?_cons, List.tail_nil, List.tail_cons,
      Option.elim_none, Option.elim_some, Option.isSome_none, Option.isSome_some, ↓reduceIte])
local macro "stepPush" : tactic => `(tactic|
  refine StackRuns.cons (StackStep.push (show code _ = .push _ _ _ from rfl)) ?_ <;>
    simp only [at_port, bank])

private theorem clear_run (w bs val : List Bool) :
    StackRuns code (val.length+1) .clear (bank w bs val [] []) .scan (bank w bs [] [] []) := by
  induction val with
  | nil => stepPop; exact .nil ..
  | cons b val ih => stepPop; exact ih

private theorem restore_run (w bs val saved collected : List Bool) :
    StackRuns code (2*saved.length+1) .restore (bank w bs val saved collected)
      .output (bank (saved.reverse ++ w) bs val [] collected) := by
  induction saved generalizing w with
  | nil => stepPop; exact .nil ..
  | cons b saved ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*saved.length+2+1 = (2*saved.length+1)+1+1 by omega]
    stepPop
    stepPush
    simpa [List.append_assoc] using ih (b::w)

private theorem output_run (w bs val collected : List Bool) :
    StackRuns code (2*collected.length+1) .output (bank w bs val [] collected)
      .done (bank w bs (collected.reverse ++ val) [] []) := by
  induction collected generalizing val with
  | nil => stepPop; exact .nil ..
  | cons b collected ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*collected.length+2+1 = (2*collected.length+1)+1+1 by omega]
    stepPop
    stepPush
    simpa [List.append_assoc] using ih (b::val)

private theorem collect_run (w data tail saved collected : List Bool) (h : data.length = w.length) :
    StackRuns code (4*w.length+1) .scan (bank w (data ++ tail) [] saved collected)
      .restore (bank [] tail [] (w.reverse ++ saved) (data.reverse ++ collected)) := by
  induction w generalizing data saved collected with
  | nil =>
    have hd : data = [] := by simpa using h
    subst data
    stepPop
    exact .nil ..
  | cons a w ih =>
    cases data with
    | nil => simp at h
    | cons b data =>
      rw [List.length_cons, Nat.mul_succ, show 4*w.length+4+1 = (4*w.length+1)+1+1+1+1 by omega]
      simp only [List.cons_append]
      stepPop
      stepPop
      stepPush
      stepPush
      simpa [List.append_assoc] using ih data (a::saved) (b::collected) (by simpa using h)

theorem read_run (w data tail old : List Bool) (h : data.length = w.length) :
    StackRuns code (old.length+8*w.length+4) .clear (bank w (data ++ tail) old [] [])
      .done (bank w tail data [] []) := by
  have h₁ := clear_run w (data ++ tail) old
  have h₂ := collect_run w data tail [] [] h
  have h₃ := restore_run [] tail [] w.reverse data.reverse
  have h₄ := output_run w tail [] data.reverse
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse, h] at h₂ h₃ h₄
  have run := ((h₁.trans h₂).trans h₃).trans h₄
  convert run using 1
  omega

private theorem collect_short (w bs saved collected : List Bool) (h : bs.length < w.length) :
    ∃ out, StackRuns code (4*bs.length+2) .scan (bank w bs [] saved collected) .reject out := by
  induction bs generalizing w saved collected with
  | nil =>
    cases w with
    | nil => simp at h
    | cons a w => refine ⟨bank w [] [] saved collected, ?_⟩; stepPop; stepPop; exact .nil ..
  | cons b bs ih =>
    cases w with
    | nil => simp at h
    | cons a w =>
      obtain ⟨out, run⟩ := ih w (a::saved) (b::collected) (by simpa using h)
      refine ⟨out, ?_⟩
      rw [List.length_cons, Nat.mul_succ, show 4*bs.length+4+2 = (4*bs.length+2)+1+1+1+1 by omega]
      stepPop
      stepPop
      stepPush
      stepPush
      exact run

theorem short_run (w bs old : List Bool) (h : bs.length < w.length) :
    ∃ out, StackRuns code (old.length+4*bs.length+3) .clear (bank w bs old [] []) .reject out := by
  obtain ⟨out, run⟩ := collect_short w bs [] [] h
  refine ⟨out, ?_⟩
  convert (clear_run w bs old).trans run using 1
  omega

end RAMTape.ProbeWord

end VPVNP
end Computability
end OAI
