import OAI.Computability.BorderVNP.TeamGuessWord
import OAI.Computability.BorderVNP.TeamPrivateFragment

/-! # Exact choice-bit consumption of a team word guess

A guessed previous word has one binary spelling. The spelling is consumed by the actual
named-stack rows, with all continuation choices left untouched. Its reverse is the order
in which bits were pushed on the result stack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamGuessWord

open VPVNP.RAMTape TeamPrivateFragment

variable {K Q : Type} [DecidableEq K]

private theorem set_bank (w s out bits : List Bool) (p : Port) :
    Function.update (bank w s out) p bits = match p with
      | .width => bank bits s out | .saved => bank w bits out | .out => bank w s bits := by
  funext j; cases p <;> cases j <;> rfl

private theorem collect (target : StackCode K Q) (ports : Port → K) (hp : Function.Injective ports)
    (labels : State → Q) (base : Stacks K) (rows : ∀ q, q ≠ .done → target (labels q) = (code q).rename ports labels)
    (w data saved out suffix : List Bool) (len : data.length = w.length) :
    StackRuns (replay target) (4*w.length+1) (labels .scan, data++suffix) (installStacks ports base (bank w saved out))
      (labels .restore, suffix) (installStacks ports base (bank [] (w.reverse++saved) (data.reverse++out))) := by
  induction w generalizing data saved out with
  | nil =>
    have he : data = [] := List.length_eq_zero_iff.mp len
    subst data
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append, List.reverse_nil]
    refine .cons (.pop (k := ports .width) (f := fun b => (labels (b.elim .restore .save), suffix)) ?_) ?_
    · simp [replay, rows .scan (by decide), code, Function.comp_def]
    · simp only [installStacks_at hp, bank, List.head?_nil, List.tail_nil, Option.elim_none, installStacks_update hp, set_bank]
      exact .nil ..
  | cons a w ih =>
    cases data with
    | nil => simp at len
    | cons b data =>
      have step := ih data (a::saved) (b::out) (by simpa using len)
      rw [List.length_cons, show 4*(w.length+1)+1 = ((((4*w.length+1)+1)+1)+1)+1 by omega]
      let rest := data++suffix
      change StackRuns (replay target) _ (labels .scan, b::rest) _ _ _
      refine .cons (.pop (k := ports .width) (f := fun z => (labels (z.elim .restore .save), b::rest)) ?_) ?_
      · simp [replay, rows .scan (by decide), code, Function.comp_def]
      simp only [installStacks_at hp, bank, List.head?_cons, List.tail_cons, Option.elim_some,
        installStacks_update hp, set_bank]
      refine .cons (.push (k := ports .saved) (b := a) (q' := (labels .choose, b::rest)) ?_) ?_
      · simp [replay, rows (.save a) (by simp), code]
      simp only [installStacks_at hp, bank, installStacks_update hp, set_bank]
      refine .cons (.goto (q' := (labels (.write b), rest)) ?_) ?_
      · cases b <;> simp [replay, rows .choose (by decide), code]
      refine .cons (.push (k := ports .out) (b := b) (q' := (labels .scan, rest)) ?_) ?_
      · simp [replay, rows (.write b) (by simp), code]
      simp only [installStacks_at hp, bank, installStacks_update hp, set_bank, List.reverse_cons, List.append_assoc, List.singleton_append]
      exact step

/-- The real choice tape spells the old word in reverse push order. The template word is
restored and exactly those bits are consumed before the caller regains control. -/
theorem replay_runs (target : StackCode K Q) (ports : Port → K) (hp : Function.Injective ports)
    (labels : State → Q) (base : Stacks K) (rows : ∀ q, q ≠ .done → target (labels q) = (code q).rename ports labels)
    (w value suffix : List Bool) (len : value.length = w.length) :
    StackRuns (replay target) (6*w.length+2) (labels .scan, value.reverse++suffix)
      (installStacks ports base (bank w [] [])) (labels .done, suffix)
      (installStacks ports base (bank w [] value)) := by
  have start := collect target ports hp labels base rows w value.reverse [] [] suffix (by simpa using len)
  have restore := (restore_run [] w.reverse value).lift ports hp labels base
    (fun q h => rows q (fun e => by subst q; contradiction))
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at start restore
  have h := start.trans (replay_segment restore suffix)
  simpa only [show 4*w.length+1+(2*w.length+1) = 6*w.length+2 by omega] using h

end TeamGuessWord

end BorderVNP
end Computability
end OAI
