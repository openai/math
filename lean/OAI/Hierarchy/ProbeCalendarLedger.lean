import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace OAI
/-! # The signed price account for the actual calendar of repair attempts

An interval is exhausted when every one of its scheduled attempts takes mode
two or three. Before the first exhausted interval, feed steps use the regular
allowance. At that interval the full repair saving pays for all remaining
crude charges. All intervals still run to the end of the calendar.
-/

namespace Hierarchy.ProbeCalendarLedger

open scoped BigOperators

def active (mode : ℕ) : Prop := mode = 2 ∨ mode = 3

def exhaust (mode : ℕ → ℕ → ℕ) (fuel j : ℕ) : Prop := ∀ h < fuel, active (mode j h)

def past (mode : ℕ → ℕ → ℕ) (fuel j : ℕ) : Prop := ∃ i < j, exhaust mode fuel i

@[simp] theorem not_past_zero (mode : ℕ → ℕ → ℕ) (fuel : ℕ) : ¬past mode fuel 0 := by
  simp [past]

theorem past_succ (mode : ℕ → ℕ → ℕ) (fuel j : ℕ) :
    past mode fuel (j + 1) ↔ past mode fuel j ∨ exhaust mode fuel j := by
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | rfl
    · exact Or.inl ⟨i, h, hx⟩
    · exact Or.inr hx
  · rintro (⟨i, hi, hx⟩ | h)
    · exact ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact ⟨j, Nat.lt_succ_self j, h⟩

/-- Telescope all actual attempts in one interval; exhaustion earns every repair gain. -/
theorem attempt_telescope (fuel : ℕ) (mode : ℕ → ℕ) (price : ℕ → ℝ) (gain : ℝ)
    (hg : 0 ≤ gain) (valid : ∀ h < fuel, mode h ≤ 3)
    (idle : ∀ h < fuel, (mode h = 0 ∨ mode h = 1) → price (h + 1) ≤ price h)
    (drop : ∀ h < fuel, active (mode h) → price (h + 1) ≤ price h - gain) :
    price fuel ≤ price 0 ∧
      ((∀ h < fuel, active (mode h)) → price fuel ≤ price 0 - (fuel : ℝ) * gain) := by
  have one (h : ℕ) (hh : h < fuel) : price (h + 1) ≤ price h := by
    by_cases ha : active (mode h)
    · linarith [drop h hh ha]
    · have range := valid h hh
      unfold active at ha
      exact idle h hh (by omega)
  have weak (h : ℕ) (hh : h ≤ fuel) : price h ≤ price 0 := by
    induction h with
    | zero => exact le_rfl
    | succ h ih => exact (one h (by omega)).trans (ih (by omega))
  refine ⟨weak fuel le_rfl, ?_⟩
  intro allActive
  have strong (h : ℕ) (hh : h ≤ fuel) : price h ≤ price 0 - (h : ℝ) * gain := by
    induction h with
    | zero => simp
    | succ h ih =>
      have lt : h < fuel := by omega
      have prev := ih lt.le
      have next := drop h lt (allActive h lt)
      rw [Nat.cast_succ, add_mul, one_mul]
      linarith
  exact strong fuel le_rfl

/-- The calendar finishes below the given bound, including when an early
exhausted interval causes all subsequent feeds to use crude charges. -/
theorem calendar_paid (total fuel : ℕ) (mode : ℕ → ℕ → ℕ)
    (priceStart priceExit allow crude : ℕ → ℝ) {upper floor gain : ℝ}
    (allowNonneg : ∀ j < total, 0 ≤ allow j) (crudeNonneg : ∀ j < total, 0 ≤ crude j)
    (regularBudget : priceStart 0 + (∑ j ∈ Finset.range total, allow j) ≤ upper)
    (fuelBudget : upper - (fuel : ℝ) * gain ≤ floor)
    (crudeBudget : floor + (∑ j ∈ Finset.range total, crude j) ≤ upper)
    (inside : ∀ j < total, priceExit j ≤ priceStart j)
    (saved : ∀ j < total, exhaust mode fuel j → priceExit j ≤ priceStart j - (fuel : ℝ) * gain)
    (regular : ∀ j < total, ¬past mode fuel j → ¬exhaust mode fuel j →
      priceStart (j + 1) ≤ priceExit j + allow j)
    (coarse : ∀ j < total, priceStart (j + 1) ≤ priceExit j + crude j) :
    priceStart total ≤ upper := by
  let sum (cost : ℕ → ℝ) (j : ℕ) := ∑ i ∈ Finset.range j, cost i
  have regularCap (j : ℕ) (hj : j ≤ total) : priceStart 0 + sum allow j ≤ upper := by
    have mono : sum allow j ≤ sum allow total := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hj) (fun i hi _ => allowNonneg i (Finset.mem_range.mp hi))
    exact (add_le_add le_rfl mono).trans regularBudget
  have inv (j : ℕ) (hj : j ≤ total) :
      (¬past mode fuel j → priceStart j ≤ priceStart 0 + sum allow j) ∧
      (past mode fuel j → priceStart j ≤ floor + sum crude j) := by
    induction j with
    | zero => simp [sum]
    | succ j ih =>
      have lt : j < total := by omega
      obtain ⟨before, after⟩ := ih lt.le
      have aNext : sum allow (j + 1) = sum allow j + allow j := Finset.sum_range_succ ..
      have cNext : sum crude (j + 1) = sum crude j + crude j := Finset.sum_range_succ ..
      constructor
      · intro hn
        have miss := mt (past_succ mode fuel j).mpr hn
        have old := before (fun h => miss (.inl h))
        have feed := regular j lt (fun h => miss (.inl h)) (fun h => miss (.inr h))
        rw [aNext]
        linarith [inside j lt]
      · intro hp
        rw [cNext]
        by_cases previous : past mode fuel j
        · linarith [after previous, inside j lt, coarse j lt]
        · have hit := ((past_succ mode fuel j).mp hp).resolve_left previous
          have start := (before previous).trans (regularCap j lt.le)
          have exit := saved j lt hit
          have paid : 0 ≤ sum crude j :=
            Finset.sum_nonneg (fun i hi => crudeNonneg i ((Finset.mem_range.mp hi).trans lt))
          linarith [coarse j lt]
  obtain ⟨before, after⟩ := inv total le_rfl
  by_cases hp : past mode fuel total
  · exact (after hp).trans crudeBudget
  · exact (before hp).trans regularBudget


end Hierarchy.ProbeCalendarLedger

end OAI
