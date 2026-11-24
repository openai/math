import OAI.Computability.VPVNP.StructuredStackTotal
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum

/-!
# Generating the bounded private-choice stream

One accepting computation of the site validator consumes exactly one finite
list of guessed bits. This table generates each list up to the public bound
once. The budget is a unary stack. After the stop choice the routine drains
the remaining budget deterministically, with the same instruction count on
every path. The continuation receives the complete guessed list.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProcessorChoices

/-- Finite controls for choosing a bounded private stream and draining the remaining budget. -/
inductive State where
  | active | stopOrContinue | toss | emit (b : Bool)
  | stopFirst | stopSecond | inactive | waitOne | waitTwo | waitThree
  deriving Fintype

variable {K : Type*}

/-- Generate each allowed bit list once and pass it to the continuation. -/
def routine (budget bits : K) : Routine K State where
  entry := .active
  code
    | .active => .pop budget (fun x => if x.isSome then some .stopOrContinue else none)
    | .stopOrContinue => .choose (some .stopFirst) (some .toss)
    | .stopFirst => .goto (some .stopSecond)
    | .stopSecond => .goto (some .inactive)
    | .toss => .choose (some (.emit false)) (some (.emit true))
    | .emit b => .push bits b (some .active)
    | .inactive => .pop budget (fun x => if x.isSome then some .waitOne else none)
    | .waitOne => .goto (some .waitTwo)
    | .waitTwo => .goto (some .waitThree)
    | .waitThree => .goto (some .inactive)

/-- Lists are grouped by the last chosen bit, which is at the bottom of the
generated stack. -/
def words : ℕ → List (List Bool)
  | 0 => [[]]
  | n+1 => [] :: ((words n).map (· ++ [false]) ++ (words n).map (· ++ [true]))

theorem mem_words (w : List Bool) (n : ℕ) : w ∈ words n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    rw [words, List.mem_cons, List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (rfl | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> simp_all
    · intro h
      induction w using List.reverseRecOn with
      | nil => exact .inl rfl
      | append_singleton s b _ =>
        have hs := (ih s).mpr (by simp at h; omega)
        cases b
        · exact .inr (.inl ⟨s, hs, rfl⟩)
        · exact .inr (.inr ⟨s, hs, rfl⟩)

theorem words_nodup (n : ℕ) : (words n).Nodup := by
  induction n with
  | zero => simp [words]
  | succ n ih =>
    rw [words, List.nodup_cons, List.nodup_append]
    refine ⟨by simp, ih.map (fun a b h => List.append_cancel_right h),
      ih.map (fun a b h => List.append_cancel_right h), ?_⟩
    intro a ha b hb heq
    subst b
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨u, _, he⟩ := List.mem_map.mp hb
    have hh := congrArg List.getLast? he
    simp at hh

variable [DecidableEq K] (budget bits : K) (hne : budget ≠ bits)

private def store (base : Stacks K) (credits guess : List Bool) :=
  Function.update (Function.update base budget credits) bits guess

include hne in
private theorem credits_at (base : Stacks K) (credits guess : List Bool) :
    store budget bits base credits guess budget = credits := by
  simp [store, Function.update_of_ne hne]

private theorem guess_at (base : Stacks K) (credits guess : List Bool) :
    store budget bits base credits guess bits = guess := by simp [store]

include hne in
private theorem put_credit (base : Stacks K) (old new guess : List Bool) :
    Function.update (store budget bits base old guess) budget new = store budget bits base new guess := by
  simp [store, Function.update_comm hne.symm]

private theorem put_guess (base : Stacks K) (credits old new : List Bool) :
    Function.update (store budget bits base credits old) bits new = store budget bits base credits new := by
  simp [store]

include hne in
private theorem inactive_count (base : Stacks K) (credits guess : List Bool)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) :
    (routine budget bits).countFrom c (t + 4*credits.length + 1) (some .inactive)
      (store budget bits base credits guess) = c t (store budget bits base [] guess) := by
  induction credits with
  | nil => simp [routine, Routine.countFrom, credits_at budget bits hne, put_credit budget bits hne]
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ]
    rw [show t + (4*xs.length+4) + 1 = (t+4*xs.length+1)+1+1+1+1 by omega]
    simpa only [Routine.countFrom, routine, credits_at budget bits hne, List.head?_cons,
      Option.isSome_some, ↓reduceIte, List.tail_cons, put_credit budget bits hne] using ih

include hne in
private theorem active_step (base : Stacks K) (credit : Bool) (xs guess : List Bool)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) :
    (routine budget bits).countFrom c (t+1+1+1+1) (some .active)
      (store budget bits base (credit :: xs) guess) =
      (routine budget bits).countFrom c t (some .inactive) (store budget bits base xs guess) +
      ((routine budget bits).countFrom c t (some .active) (store budget bits base xs (false :: guess)) +
      (routine budget bits).countFrom c t (some .active) (store budget bits base xs (true :: guess))) := by
  simp only [Routine.countFrom, routine, credits_at budget bits hne, List.head?_cons,
    Option.isSome_some, ↓reduceIte, List.tail_cons, put_credit budget bits hne, guess_at, put_guess]

include hne in
private theorem active_count (base : Stacks K) (credits guess : List Bool)
    (c : ℕ → Stacks K → ℕ) (t : ℕ) :
    (routine budget bits).countFrom c (t + 4*credits.length + 1) (some .active)
      (store budget bits base credits guess) =
      ((words credits.length).map (fun bs => c t (store budget bits base [] (bs ++ guess)))).sum := by
  induction credits generalizing guess with
  | nil => simp [routine, Routine.countFrom, words, credits_at budget bits hne, put_credit budget bits hne]
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ]
    rw [show t + (4*xs.length+4) + 1 = (t+4*xs.length+1)+1+1+1+1 by omega]
    rw [active_step budget bits hne, inactive_count budget bits hne, ih, ih]
    simp [words, Function.comp_def, List.append_assoc]

include hne in
/-- Exact CPS count, with the budget and output ports explicit in the caller. -/
theorem count (base : Stacks K) (credits : List Bool) (c : ℕ → Stacks K → ℕ) (t : ℕ) :
    (routine budget bits).count c (t+4*credits.length+1)
      (Function.update (Function.update base budget credits) bits []) =
      ((words credits.length).map (fun bs => c t (Function.update (Function.update base budget []) bits bs))).sum := by
  simpa [Routine.count, store, routine] using active_count budget bits hne base credits [] c t

include hne in
private theorem inactive_stops (base : Stacks K) (credits guess : List Bool)
    (c : ℕ → Stacks K → Prop) (t : ℕ) :
    (routine budget bits).AllStopsFrom c (t + 4*credits.length + 1) (some .inactive)
      (store budget bits base credits guess) ↔ c t (store budget bits base [] guess) := by
  induction credits with
  | nil => simp [routine, Routine.AllStopsFrom, credits_at budget bits hne, put_credit budget bits hne]
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ]
    rw [show t + (4*xs.length+4) + 1 = (t+4*xs.length+1)+1+1+1+1 by omega]
    simpa only [Routine.AllStopsFrom, routine, credits_at budget bits hne, List.head?_cons,
      Option.isSome_some, ↓reduceIte, List.tail_cons, put_credit budget bits hne] using ih

include hne in
private theorem active_stops_step (base : Stacks K) (credit : Bool) (xs guess : List Bool)
    (c : ℕ → Stacks K → Prop) (t : ℕ) :
    (routine budget bits).AllStopsFrom c (t+1+1+1+1) (some .active)
      (store budget bits base (credit :: xs) guess) ↔
      (routine budget bits).AllStopsFrom c t (some .inactive) (store budget bits base xs guess) ∧
      (routine budget bits).AllStopsFrom c t (some .active) (store budget bits base xs (false :: guess)) ∧
      (routine budget bits).AllStopsFrom c t (some .active) (store budget bits base xs (true :: guess)) := by
  simp only [Routine.AllStopsFrom, routine, credits_at budget bits hne, List.head?_cons,
    Option.isSome_some, ↓reduceIte, List.tail_cons, put_credit budget bits hne, guess_at, put_guess]

include hne in
private theorem active_stops (base : Stacks K) (credits guess : List Bool)
    (c : ℕ → Stacks K → Prop) (t : ℕ) :
    (routine budget bits).AllStopsFrom c (t + 4*credits.length + 1) (some .active)
      (store budget bits base credits guess) ↔
      ∀ bs ∈ words credits.length, c t (store budget bits base [] (bs ++ guess)) := by
  induction credits generalizing guess with
  | nil => simp [routine, Routine.AllStopsFrom, words, credits_at budget bits hne, put_credit budget bits hne]
  | cons b xs ih =>
    simp only [List.length_cons, Nat.mul_succ]
    rw [show t + (4*xs.length+4) + 1 = (t+4*xs.length+1)+1+1+1+1 by omega]
    rw [active_stops_step budget bits hne, inactive_stops budget bits hne, ih, ih]
    simp only [words, List.forall_mem_cons, List.forall_mem_append, List.forall_mem_map,
      List.nil_append, List.append_assoc, List.singleton_append]

include hne in
/-- Every generator branch spends exactly the same prefix cost. The remaining
budget suffices exactly when the continuation stops on each permitted list. -/
theorem allStops_iff (base : Stacks K) (credits : List Bool) (c : ℕ → Stacks K → Prop) (t : ℕ) :
    (routine budget bits).AllStops c (t+4*credits.length+1)
      (Function.update (Function.update base budget credits) bits []) ↔
      ∀ bs : List Bool, bs.length ≤ credits.length →
        c t (Function.update (Function.update base budget []) bits bs) := by
  simpa only [Routine.AllStops, routine, store, mem_words, List.append_nil] using
    active_stops budget bits hne base credits [] c t

end RAMTape.ProcessorChoices

end VPVNP
end Computability
end OAI
