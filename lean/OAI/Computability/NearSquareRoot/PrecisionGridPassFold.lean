import OAI.Computability.IntegerMultiplication.Code.FoldLeft
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # A single stack program for consecutive phase-table passes

The unswept suffix of the forest determines the pass index in the correctness
proof. The program traverses the supplied tables, so the number of passes and
their indices do not occur in its finite control.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication.Code
open IntegerMultiplication.Code.Task (forest foldCost)

/-- The indices of the unread tables in a left-to-right traversal. -/
private def remaining (d : ℕ) (l : List ℕ) : Prop :=
  l = List.range' (d - l.length) l.length ∧ l.length ≤ d

private theorem remaining_step {d j : ℕ} {l : List ℕ} (h : remaining d (j :: l)) :
    remaining d l ∧ j = d - (l.length + 1) ∧ d - l.length = j + 1 ∧ j < d := by
  obtain ⟨eq, hl⟩ := h
  rw [List.length_cons, List.range'_succ] at eq
  rw [List.length_cons] at hl
  obtain ⟨hj, htail⟩ := List.cons.inj eq
  have next : d - l.length = j + 1 := by omega
  exact ⟨⟨by simpa only [next, ← hj] using htail, by omega⟩, hj, next, by omega⟩

theorem indexedFoldCost (f : ℕ → ℕ) (n : ℕ) :
    foldCost (fun j _ => f j) (List.range n) = (∑ j ∈ Finset.range n, (f j + 1)) + 1 := by
  have hs (l : List ℕ) : foldCost (fun j _ => f j) l = costSum (fun j => f j + 1) l + 1 := by
    induction l with
    | nil => rfl
    | cons j l ih => simp only [foldCost, costSum_cons, ih]; omega
  rw [hs]
  congr 1

/-- Given one uniform implementation for each step of an indexed sequence, run
all steps on the supplied ordered table forest. The bound includes transferring
each table from the forest and one list delimiter per table. -/
theorem indexedPasses {I : Type*} (d : I → ℕ) (table state : I → ℕ → Tree)
    (cost : I → ℕ → ℕ)
    (step : Task (fun x : (i : I) × Fin (d i) => cost x.1 x.2.val)
      (fun x => .fork (table x.1 x.2.val) (state x.1 x.2.val))
      (fun x => state x.1 (x.2.val + 1))) :
    Task (fun i => (∑ j ∈ Finset.range (d i), (cost i j + (table i j).count + 1)) + 1)
      (fun i => .fork (forest (table i) (List.range (d i))) (state i 0))
      (fun i => state i (d i)) := by
  let w (l : List ℕ) (i : I) := state i (d i - l.length)
  have H := Task.sweep (p := table) (w := w) (a := fun j _ i => cost i j)
    (D := fun l i => remaining (d i) l)
    (fun _ _ _ h => (remaining_step h).1) (show Task _ _ _ from ?_)
  · let start (i : I) : {s : List ℕ × I // remaining (d s.2) s.1} :=
      ⟨(List.range (d i), i), by simp [remaining, List.range_eq_range']⟩
    exact (H.on start).conform (fun i => indexedFoldCost _ (d i))
      (by simp [w, start]) (by simp [w, start])
  · let idx (e : {s : ℕ × List ℕ × I // remaining (d s.2.2) (s.1 :: s.2.1)}) :
        (i : I) × Fin (d i) := ⟨e.val.2.2, ⟨e.val.1, (remaining_step e.property).2.2.2⟩⟩
    apply (step.on idx).conform (fun _ => rfl)
    · intro e
      simp only [idx, w, List.length_cons, ← (remaining_step e.property).2.1]
    · intro e
      simp only [idx, w, (remaining_step e.property).2.2.1]

end FixedPoint

end NearSquareRoot
end Computability
end OAI
