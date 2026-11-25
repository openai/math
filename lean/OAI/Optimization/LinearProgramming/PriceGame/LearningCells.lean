import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Cells

open Finset

/-- The initial interval, or an observed threshold and a bit indicating
whether the value equals that threshold or lies in the interval above it. -/
abbrev Cell {α : Type*} (thresholds : Finset α) := Option (↥thresholds × Bool)

variable {α : Type*} [LinearOrder α]

/-- Encode a feature value by its predecessor among the observed thresholds. -/
def encode (thresholds : Finset α) (x : α) : Cell thresholds :=
  let below := thresholds.filter (· ≤ x)
  if h : below.Nonempty then
    some (⟨below.max' h, (mem_filter.mp (below.max'_mem h)).1⟩, decide (x = below.max' h))
  else none

/-- Recover a three-way comparison from a cell and an observed threshold. -/
def decode {thresholds : Finset α} (c : Cell thresholds) (θ : α) : Ordering :=
  match c with
  | none => .lt
  | some (pred, hit) =>
    if θ < pred.val then .gt
    else if θ = pred.val then (if hit then .eq else .gt)
    else .lt

theorem decode_encode (thresholds : Finset α) (x : α) {θ : α} (hθ : θ ∈ thresholds) :
    decode (encode thresholds x) θ = compare x θ := by
  let below := thresholds.filter (· ≤ x)
  by_cases h : below.Nonempty
  · have hm : below.max' h ≤ x := (mem_filter.mp (below.max'_mem h)).2
    rw [encode, dite_eq_left h]
    change (if θ < below.max' h then Ordering.gt else if θ = below.max' h then
      (if decide (x = below.max' h) then Ordering.eq else Ordering.gt) else Ordering.lt) = _
    rcases lt_trichotomy θ (below.max' h) with ht | ht | ht
    · rw [ite_eq_left ht]
      exact (compare_gt_iff_gt.mpr (ht.trans_le hm)).symm
    · subst θ
      by_cases hx : x = below.max' h
      · simp [hx]
      · simpa [hx] using (compare_gt_iff_gt.mpr (lt_of_le_of_ne hm (Ne.symm hx))).symm
    · have hx : x < θ := by
        by_contra! he
        have hmθ : θ ∈ below := mem_filter.mpr ⟨hθ, he⟩
        exact (not_le_of_gt ht) (below.le_max' θ hmθ)
      simpa [not_lt_of_ge ht.le, ne_of_gt ht] using (compare_lt_iff_lt.mpr hx).symm
  · have hx : x < θ := by
      by_contra! hle
      exact h ⟨θ, mem_filter.mpr ⟨hθ, hle⟩⟩
    rw [encode, dite_eq_right h]
    exact (compare_lt_iff_lt.mpr hx).symm

omit [LinearOrder α] in
@[simp] theorem card_cell (thresholds : Finset α) :
    Fintype.card (Cell thresholds) = 2 * thresholds.card + 1 := by
  simp [Cell, Fintype.card_option, Nat.mul_comm]

/-- The candidates enumerated when choosing one part for each feature.
Several codes can be ruled out later by difference-constraint feasibility. -/
def enumerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thresholds : ι → Finset α) : Finset ((i : ι) → Cell (thresholds i)) :=
  univ

theorem contains_comparison_pattern {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thresholds : ι → Finset α) (values : ι → α) :
    ∃ c ∈ enumerate thresholds, ∀ i θ, θ ∈ thresholds i → decode (c i) θ = compare (values i) θ := by
  exact ⟨fun i => encode (thresholds i) (values i), mem_univ _, fun i _θ => decode_encode _ _⟩

omit [LinearOrder α] in
theorem card_enumerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thresholds : ι → Finset α) :
    (enumerate thresholds).card = ∏ i, (2 * (thresholds i).card + 1) := by
  simp [enumerate, Fintype.card_pi, Nat.mul_comm]

omit [LinearOrder α] in
theorem card_enumerate_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thresholds : ι → Finset α) (k : ℕ) (hk : ∀ i, (thresholds i).card ≤ k) :
    (enumerate thresholds).card ≤ (2 * k + 1) ^ Fintype.card ι := by
  rw [card_enumerate]
  calc
    ∏ i, (2 * (thresholds i).card + 1) ≤ ∏ _i : ι, (2 * k + 1) :=
      prod_le_prod (fun i _ => by have := hk i; omega)
    _ = _ := by simp

omit [LinearOrder α] in
/-- For a constant number `d` of features, a uniform polynomial bound on
observed thresholds gives an explicit polynomial bound on the number of cells. -/
theorem card_enumerate_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (thresholds : ι → Finset α) (X c d : ℕ) (hX : 3 ≤ X)
    (hd : Fintype.card ι ≤ d) (hk : ∀ i, (thresholds i).card ≤ X ^ c) :
    (enumerate thresholds).card ≤ X ^ ((c + 1) * d) := by
  have hXp : 0 < X := by omega
  have hXc : 0 < X ^ c := pow_pos hXp _
  have hbase : 2 * X ^ c + 1 ≤ X ^ (c + 1) := by
    rw [pow_succ]
    have := Nat.mul_le_mul_left (X ^ c) hX
    omega
  calc
    (enumerate thresholds).card ≤ (2 * X ^ c + 1) ^ Fintype.card ι :=
      card_enumerate_le thresholds (X ^ c) hk
    _ ≤ (X ^ (c + 1)) ^ Fintype.card ι := Nat.pow_le_pow_left hbase _
    _ = X ^ ((c + 1) * Fintype.card ι) := (pow_mul _ _ _).symm
    _ ≤ X ^ ((c + 1) * d) :=
      Nat.pow_le_pow_right hXp (Nat.mul_le_mul_left _ hd)

end Cells
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
