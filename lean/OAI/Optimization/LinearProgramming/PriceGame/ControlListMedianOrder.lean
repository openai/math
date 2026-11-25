import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionTypes
import Mathlib.Data.List.Sort

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

/-- Inserting after every previous equal value gives a stable ascending order. -/
def insertMedianValue (x : ℚ) (xs : List ℚ) : List ℚ :=
  xs.filter (fun z => decide (z ≤ x)) ++ x :: xs.filter (fun z => decide (x < z))

private theorem insertMedian_perm (x : ℚ) (xs : List ℚ) :
    (insertMedianValue x xs).Perm (x :: xs) := by
  unfold insertMedianValue
  apply List.perm_middle.trans
  apply List.Perm.cons
  have hc : (fun z : ℚ => !decide (z ≤ x)) = fun z => decide (x < z) := by
    funext z
    by_cases hz : z ≤ x
    · simp [hz, not_lt_of_ge hz]
    · simp [hz, lt_of_not_ge hz]
  simpa only [hc] using (List.filter_append_perm (fun z : ℚ => decide (z ≤ x)) xs)

private theorem insertMedian_sorted (x : ℚ) (xs : List ℚ) (h : xs.Pairwise (· ≤ ·)) :
    (insertMedianValue x xs).Pairwise (· ≤ ·) := by
  simp only [insertMedianValue, List.pairwise_append, List.pairwise_cons]
  refine ⟨h.filter _, ⟨?_, h.filter _⟩, ?_⟩
  · intro y hy
    exact (of_decide_eq_true (List.mem_filter.mp hy).2).le
  · intro y hy z hz
    have hyx : y ≤ x := of_decide_eq_true (List.mem_filter.mp hy).2
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hyx
    · exact hyx.trans (of_decide_eq_true (List.mem_filter.mp hz).2).le

/-- Ascending order including the full multiplicity of every rational. -/
def sortMedianValues (xs : List ℚ) : List ℚ :=
  xs.foldl (fun acc x => insertMedianValue x acc) []

theorem medianFold_perm (xs acc : List ℚ) :
    (xs.foldl (fun acc x => insertMedianValue x acc) acc).Perm (xs ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    exact (ih _).trans (((insertMedian_perm x acc).append_left xs).trans List.perm_middle)

private theorem sortFold_sorted (xs acc : List ℚ) (ha : acc.Pairwise (· ≤ ·)) :
    (xs.foldl (fun acc x => insertMedianValue x acc) acc).Pairwise (· ≤ ·) := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih => exact ih _ (insertMedian_sorted x acc ha)

private theorem sorted_ofFn_eq {n : ℕ} (f : Fin n → ℚ) :
    sortMedianValues (List.ofFn f) = List.ofFn (f ∘ Tuple.sort f) := by
  have hp : (sortMedianValues (List.ofFn f)).Perm (List.ofFn f) := by
    simpa [sortMedianValues] using medianFold_perm (List.ofFn f) []
  apply (hp.trans ((Tuple.sort f).ofFn_comp_perm f).symm).eq_of_pairwise'
    (sortFold_sorted _ _ List.Pairwise.nil)
  exact List.pairwise_ofFn.mpr (fun _ _ h => Tuple.monotone_sort f h.le)

/-- The empty list returns zero; an even length selects the upper-middle order statistic. -/
def listMedian (xs : List ℚ) : ℚ := ((sortMedianValues xs).drop (xs.length/2)).headD 0

theorem listMedian_ofFn {n : ℕ} (f : Fin n → ℚ) :
    listMedian (List.ofFn f) = TrialExecution.median f := by
  by_cases h : 0 < n
  · have hi : n / 2 < n := by omega
    simp [listMedian, sorted_ofFn_eq, TrialExecution.median, h, hi, List.head?_drop, Function.comp_def]
  · obtain rfl : n = 0 := by omega
    simp [listMedian, sortMedianValues, TrialExecution.median]


end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
