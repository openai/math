import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Prefix images of the cache of conditional label means -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open scoped BigOperators

/-- Directory address and the two incident contributions for each bin ordinal. -/
structure PassBins where
  /-- Address of the current total in the shared cache. -/
  addr : ℕ → ℕ
  /-- Contribution to remove from the current total on committing a label. -/
  before : ℕ → ℕ
  /-- Contribution to add after committing the label. -/
  after : ℕ → ℕ

/-- Committing the first bins replaces their old incident contributions by the new ones. -/
def PassBins.image (b : PassBins) (m : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | i+1 => Function.update (b.image m i) (b.addr i)
      (b.image m i (b.addr i) - b.before i + b.after i)

/-- A bin pass leaves each address outside the visited prefix intact. -/
theorem PassBins.image_off (b : PassBins) (m : ℕ → ℕ) (i a : ℕ)
    (outside : ∀ j < i, a ≠ b.addr j) : b.image m i a = m a := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [PassBins.image, Function.update_of_ne (outside i (Nat.lt_succ_self _))]
    exact ih fun j hj => outside j (Nat.lt_succ_of_lt hj)

/-- On a directory of distinct addresses, every visited cache word has its new total. -/
theorem PassBins.image_at (b : PassBins) (m : ℕ → ℕ) (i j : ℕ) (hj : j < i)
    (distinct : ∀ x < i, ∀ y < i, b.addr x = b.addr y → x = y) :
    b.image m i (b.addr j) = m (b.addr j) - b.before j + b.after j := by
  induction i with
  | zero => omega
  | succ i ih =>
    by_cases h : j = i
    · subst j
      rw [PassBins.image, Function.update_self, b.image_off m i (b.addr i)]
      intro k hk eq
      have := distinct i (by omega) k (by omega) eq
      omega
    · have ne : b.addr j ≠ b.addr i := fun he => h (distinct j hj i (by omega) he)
      rw [PassBins.image, Function.update_of_ne ne]
      exact ih (by omega) fun x hx y hy => distinct x (by omega) y (by omega)

/-- Sum of cached mean times the trial's new incident contribution on the visited prefix. -/
def PassBins.score (b : PassBins) (m : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, m (b.addr j) * b.after j

/-- One new score term is added by advancing the bin ordinal. -/
theorem PassBins.score_succ (b : PassBins) (m : ℕ → ℕ) (i : ℕ) :
    b.score m (i+1) = b.score m i + m (b.addr i) * b.after i := by
  simp [score, Finset.sum_range_succ]

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
