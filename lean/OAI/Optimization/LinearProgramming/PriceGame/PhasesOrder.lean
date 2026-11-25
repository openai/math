import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! # Chronological intervals between exceptional trials

A trial that changes a representative terminates the current comparison interval.
The next interval begins at the following trial, including when two exceptional
trials are consecutive.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Phases

/-- The exceptional trial with zero-based rank `k` in chronological order. -/
def eventAt (s : Finset ℕ) (k : Fin s.card) : ℕ := (s.orderIsoOfFin rfl k).val

@[simp] theorem eventAt_mem (s : Finset ℕ) (k : Fin s.card) : eventAt s k ∈ s :=
  (s.orderIsoOfFin rfl k).property

theorem eventAt_strictMono (s : Finset ℕ) : StrictMono (eventAt s) :=
  fun _ _ h => (s.orderIsoOfFin rfl).strictMono h

theorem exists_eventAt_of_mem {s : Finset ℕ} {t : ℕ} (ht : t ∈ s) :
    ∃ k, eventAt s k = t :=
  ⟨(s.orderIsoOfFin rfl).symm ⟨t, ht⟩,
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨t, ht⟩)⟩

/-- Start of interval `k`, after exactly `k` exceptional trials. Inputs past the final
interval retain the terminal start. -/
def epochStart (s : Finset ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if h : k < s.card then eventAt s ⟨k, h⟩ + 1 else epochStart s k

@[simp] theorem epochStart_zero (s : Finset ℕ) : epochStart s 0 = 0 := rfl

theorem epochStart_succ (s : Finset ℕ) (k : ℕ) (hk : k < s.card) :
    epochStart s (k + 1) = eventAt s ⟨k, hk⟩ + 1 := by simp [epochStart, hk]

theorem epochStart_le_event (s : Finset ℕ) (k : Fin s.card) :
    epochStart s k ≤ eventAt s k := by
  rcases k with ⟨k, hk⟩
  cases k with
  | zero => exact Nat.zero_le _
  | succ n =>
    rw [show (↑(⟨n + 1, hk⟩ : Fin s.card) : ℕ) = n + 1 by rfl,
      epochStart_succ s n (by omega)]
    exact eventAt_strictMono s (show (⟨n, by omega⟩ : Fin s.card) < ⟨n + 1, hk⟩ by exact Nat.lt_succ_self _)

theorem epochStart_mono (s : Finset ℕ) : Monotone (epochStart s) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < s.card
  · rw [epochStart_succ s k hk]
    exact (epochStart_le_event s ⟨k,hk⟩).trans (Nat.le_succ _)
  · simp [epochStart, hk]

theorem eventAt_lt_epochStart (s : Finset ℕ) {k : ℕ} (hk : k ≤ s.card)
    (j : Fin s.card) (hj : j.val < k) : eventAt s j < epochStart s k := by
  cases k with
  | zero => omega
  | succ n =>
    rw [epochStart_succ s n (by omega)]
    exact Nat.lt_succ_of_le ((eventAt_strictMono s).monotone
      (show j ≤ (⟨n, by omega⟩ : Fin s.card) by change j.val ≤ n; omega))

/-- No exceptional trial lies between the current interval start and its ending
exceptional trial. The latter is excluded. -/
theorem not_mem_between_events (s : Finset ℕ) (k : Fin s.card) {t : ℕ}
    (lo : epochStart s k ≤ t) (hi : t < eventAt s k) : t ∉ s := by
  intro ht
  obtain ⟨j, rfl⟩ := exists_eventAt_of_mem ht
  by_cases h : j < k
  · exact (Nat.not_lt_of_ge lo) (eventAt_lt_epochStart s k.isLt.le j h)
  · exact (not_lt_of_ge ((eventAt_strictMono s).monotone (le_of_not_gt h))) hi

/-- Following the last exceptional trial, every subsequent trial is nonexceptional.
This also handles an empty set of exceptional trials. -/
theorem not_mem_after_last_event (s : Finset ℕ) {t : ℕ} (lo : epochStart s s.card ≤ t) : t ∉ s := by
  intro ht
  obtain ⟨j, rfl⟩ := exists_eventAt_of_mem ht
  exact (Nat.not_lt_of_ge lo) (eventAt_lt_epochStart s le_rfl j j.isLt)


/-- A nonempty order-convex finite collection of trials is exactly the half-open
interval bounded by its first trial and one past its last trial. -/
theorem convex_map_val_eq_Ico {T : ℕ} (s : Finset (Fin T)) (hs : s.Nonempty)
    (convex : ∀ u ∈ s, ∀ w ∈ s, ∀ v, u ≤ v → v ≤ w → v ∈ s) :
    s.map Fin.valEmbedding = Finset.Ico (s.min' hs).val ((s.max' hs).val + 1) := by
  ext t
  constructor
  · intro ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp ht
    exact Finset.mem_Ico.mpr ⟨s.min'_le _ hv, Nat.lt_succ_of_le (s.le_max' _ hv)⟩
  · intro ht
    obtain ⟨lo, hi⟩ := Finset.mem_Ico.mp ht
    have hT : t < T := (Nat.lt_succ_iff.mp hi).trans_lt (s.max' hs).isLt
    exact Finset.mem_map.mpr ⟨⟨t, hT⟩,
      convex _ (s.min'_mem hs) _ (s.max'_mem hs) _ lo (Nat.lt_succ_iff.mp hi), rfl⟩

theorem card_convex_eq_length {T : ℕ} (s : Finset (Fin T)) (hs : s.Nonempty)
    (convex : ∀ u ∈ s, ∀ w ∈ s, ∀ v, u ≤ v → v ≤ w → v ∈ s) :
    s.card = (s.max' hs).val + 1 - (s.min' hs).val := by
  simpa using congrArg Finset.card (convex_map_val_eq_Ico s hs convex)

end Phases
end PriceGame
end LinearProgramming
end Optimization
end OAI
