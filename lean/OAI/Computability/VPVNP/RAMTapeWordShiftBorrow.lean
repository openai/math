import OAI.Computability.VPVNP.RAMTapeWordShiftControl

/-!
# Subtracting one from the binary shift amount

A leading zero in the little-endian amount creates a pending one on the
scratch stack. At the first set bit, the machine clears it and restores
the pending ones. Reaching the end signals zero and clears the scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord.Shift

open RAMTape

local macro "borrow_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_store, Bool.false_eq_true, ite_false, ite_true])

private theorem clear_run (left b : Bool) (d t o s : List Bool) :
    StackRuns (code left) (s.length + 1) (.clear b) (store [] d t o s)
      (.zero b) (store [] d t o []) := by
  induction s with
  | nil => borrow_step; exact .nil ..
  | cons x s ih =>
    simp only [List.length_cons]
    borrow_step
    exact ih

private theorem restore_run (left : Bool) (a d t o s : List Bool) :
    StackRuns (code left) (2 * s.length + 1) .restore (store a d t o s)
      .consume (store (List.replicate s.length true ++ a) d t o []) := by
  induction s generalizing a with
  | nil => borrow_step; exact .nil ..
  | cons x s ih =>
    simp only [List.length_cons, Nat.mul_succ, List.replicate_succ', List.append_assoc,
      List.singleton_append]
    borrow_step
    borrow_step
    exact ih (true :: a)

private theorem borrow_pending (left b : Bool) (a d t o s : List Bool) :
    ∃ k ≤ 4 * a.length + 2 * s.length + 3,
      if value a = 0 then
        StackRuns (code left) k (.borrow b) (store a d t o s) (.zero b) (store [] d t o [])
      else ∃ a', a'.length = a.length ∧ value a' = value a - 1 ∧
        StackRuns (code left) k (.borrow b) (store a d t o s) .consume
          (store (List.replicate s.length true ++ a') d t o []) := by
  induction a generalizing s with
  | nil =>
    refine ⟨s.length + 1 + 1, by simp only [List.length_nil]; omega, ?_⟩
    simp only [value, ite_true]
    borrow_step
    exact clear_run left b d t o s
  | cons x a ih =>
    cases x with
    | true =>
      refine ⟨2 * s.length + 1 + 1 + 1, by simp only [List.length_cons]; omega, ?_⟩
      have hn : value (true :: a) ≠ 0 := by simp [value]
      simp only [hn, ↓reduceIte]
      refine ⟨false :: a, rfl, by simp [value], ?_⟩
      borrow_step
      borrow_step
      exact restore_run left (false :: a) d t o s
    | false =>
      obtain ⟨k, hk, run⟩ := ih (true :: s)
      refine ⟨k + 1 + 1, by simp only [List.length_cons] at *; omega, ?_⟩
      by_cases hz : value a = 0
      · have hz' : value (false :: a) = 0 := by simp [value, hz]
        simp only [hz', ↓reduceIte]
        simp only [hz, ↓reduceIte] at run
        borrow_step
        borrow_step
        exact run
      · have hn : value (false :: a) ≠ 0 := by simp [value, hz]
        simp only [hn, ↓reduceIte]
        simp only [hz, ↓reduceIte] at run
        obtain ⟨a', hlen, hval, hr⟩ := run
        refine ⟨true :: a', by simp [hlen], ?_, ?_⟩
        · simp only [value, Bool.toNat_true, Bool.toNat_false]
          omega
        · borrow_step
          borrow_step
          simpa only [List.length_cons, List.replicate_succ', List.append_assoc,
          List.singleton_append] using hr

/-- A positive binary shift amount decreases by one with its width preserved.
For a zero amount, the zero branch is reached with both amount and scratch empty. -/
theorem borrow_run (left b : Bool) (a d t o : List Bool) :
    ∃ k ≤ 5 * (a.length + 1) + 5,
      if value a = 0 then
        StackRuns (code left) k (.borrow b) (store a d t o []) (.zero b) (store [] d t o [])
      else ∃ a', a'.length = a.length ∧ value a' = value a - 1 ∧
        StackRuns (code left) k (.borrow b) (store a d t o []) .consume (store a' d t o []) := by
  obtain ⟨k, hk, run⟩ := borrow_pending left b a d t o []
  exact ⟨k, by simp only [List.length_nil] at hk; omega, by simpa using run⟩

end TapeWord.Shift

end VPVNP
end Computability
end OAI
