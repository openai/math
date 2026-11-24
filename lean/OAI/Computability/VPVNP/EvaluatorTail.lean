import OAI.Computability.VPVNP.ChoiceWitness
import OAI.Computability.VPVNP.CutSchedule
import Mathlib.SetTheory.Cardinal.Finite

/-!
# One evaluator transition per tail group

In Section 14.1 each live tail group executes one transition, preserving the
two choices of a branching transition even if their successor configurations
are equal. An accepting halt is serialized by one canonical configuration.
For any fixed clocked machine, the sequence of matching cut configurations
is uniquely determined by the branch choices, and the successful sequences
count exactly its accepting paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace EvaluatorTail

open UniversalMachine

/-- Accepted computations propagate a single canonical halted state down the tail. -/
inductive State (extra : ℕ) where
  | accepted
  | rejected
  | running (c : Config extra)

/-- Forget the tape contents on a halt. -/
def canonical {extra : ℕ} (c : Config extra) : State extra :=
  if c.state.val = 1 then .accepted else if c.state.val = 0 then .rejected else .running c

@[simp] theorem canonical_accepted_iff {extra : ℕ} (c : Config extra) :
    canonical c = .accepted ↔ c.state.val = 1 := by
  unfold canonical
  split_ifs <;> simp_all

/-- A padded choice zero propagates an accepting halt exactly once.
Invalid choices, including a one at an accepting halt, enter rejection. -/
def step (p : Program) (s : State p.extra) (bit : Bool) : State p.extra :=
  match s with
  | .accepted => if bit then .rejected else .accepted
  | .rejected => .rejected
  | .running c => canonical (choiceStep p c bit)

theorem step_canonical (p : Program) (c : Config p.extra) (bit : Bool) :
    step p (canonical c) bit = canonical (choiceStep p c bit) := by
  by_cases ha : c.state.val = 1
  · cases bit <;> simp [canonical, ha, step, choiceStep, reject]
  · by_cases hr : c.state.val = 0
    · simp [canonical, hr, step, choiceStep]
    · simp [canonical, ha, hr, step]

/-- The initial configuration and one output configuration per tail group. -/
def history (p : Program) : (t : ℕ) → Config p.extra → (Fin t → Bool) → Fin (t + 1) → State p.extra
  | 0, c, _ => fun _ => canonical c
  | t + 1, c, w => Fin.cons (canonical c) (history p t (choiceStep p c (w 0)) (Fin.tail w))

@[simp] theorem history_zero (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin t → Bool) :
    history p t c w 0 = canonical c := by cases t <;> rfl

theorem history_step (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin t → Bool) (i : Fin t) :
    history p t c w i.succ = step p (history p t c w i.castSucc) (w i) := by
  induction t generalizing c with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [history, Fin.cons_zero, Fin.cons_succ] using (step_canonical p c (w 0)).symm
    · simpa [history, Fin.tail] using ih (choiceStep p c (w 0)) (Fin.tail w) j

theorem history_last (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin t → Bool) :
    history p t c w (Fin.last t) = .accepted ↔ acceptsChoices p t c w := by
  induction t generalizing c with
  | zero => simp [history, acceptsChoices]
  | succ t ih =>
    rw [history, Fin.cons_last, acceptsChoices_succ]
    exact ih (choiceStep p c (w 0)) (Fin.tail w)

/-- Local tail checks fix every cut configuration, starting from the advised
initial configuration and executing one step per group. -/
theorem eq_history (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin t → Bool)
    (s : Fin (t + 1) → State p.extra) (hinit : s 0 = canonical c)
    (hstep : ∀ i, s i.succ = step p (s i.castSucc) (w i)) :
    s = history p t c w := by
  funext i
  induction i using Fin.induction with
  | zero => exact hinit.trans (history_zero ..).symm
  | succ j ih => rw [hstep, ih, history_step]

/-- Accepted tail choices and their matching configurations, including the
initial and final boundary values. -/
abbrev Traces (p : Program) (t : ℕ) (c : Config p.extra) :=
  (w : Fin t → Bool) × {s : Fin (t + 1) → State p.extra //
    s 0 = canonical c ∧ (∀ i, s i.succ = step p (s i.castSucc) (w i)) ∧ s (Fin.last t) = .accepted}

/-- Bijection used by the last `L/2` groups of Section 14.1. It includes an
initially accepting evaluator and every early halt. -/
def tracesEquiv (p : Program) (t : ℕ) (c : Config p.extra) :
    {w : Fin t → Bool // acceptsChoices p t c w} ≃ Traces p t c where
  toFun w := ⟨w.val, history p t c w.val, history_zero .., history_step p t c w.val,
    (history_last ..).mpr w.property⟩
  invFun s := ⟨s.1, (history_last ..).mp ((eq_history p t c s.1 s.2.val s.2.property.1
    s.2.property.2.1) ▸ s.2.property.2.2)⟩
  left_inv _ := rfl
  right_inv s := by
    rcases s with ⟨w, cuts, hi, hs, ha⟩
    have he := eq_history p t c w cuts hi hs
    subst cuts
    rfl

/-- The integer count of valid local tail transcripts equals the machine's
clocked accepting path count. -/
theorem card_traces (p : Program) (t : ℕ) (c : Config p.extra) :
    Nat.card (Traces p t c) = paths p t c := by
  rw [← Nat.card_congr (tracesEquiv p t c), Nat.card_eq_fintype_card,
    Fintype.card_subtype, paths_eq_card_choices]

/-- For a fixed encoding of the reached configuration, checking the tail
layout and zero padding leaves exactly one possible cut string. -/
theorem encoded_cut_unique (p : Program) (h Δ i csize : ℕ) (hi : 2 ^ h < i)
    (hlt : i < 2 ^ (h + 1)) (hfit : 1 + csize ≤ Δ) (encode : State p.extra → CutSchedule.Bits csize)
    (c : Config p.extra) (w : Fin (2 ^ h) → Bool) :
    ∃! bits, CutSchedule.tailLayout h Δ i csize hi.le hlt hfit bits =
      (true, encode (history p (2 ^ h) c w ⟨i - 2 ^ h, by rw [pow_succ] at hlt; omega⟩),
        fun _ => false) :=
  CutSchedule.tail_unique ..

end EvaluatorTail

end VPVNP
end Computability
end OAI
