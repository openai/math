import Mathlib.Data.Bool.Basic
import Mathlib.Order.Monotone.Basic

namespace OAI
/-! # Threshold cuts for the zero-one principle

A wire assignment is sorted exactly when it is sorted after every Boolean threshold cut.
Applying a cut to a min/max comparator commutes with evaluation, so Boolean correctness
suffices for any network built from comparators.
-/

namespace LinearAlgebra.SpectralBooks.Batcher

variable {α ι : Type*} [LinearOrder α] [Preorder ι]

/-- The bit indicating that a key lies at or above a threshold. -/
def thresholdCut (t x : α) : Bool := decide (t ≤ x)

theorem monotone_thresholdCut (t : α) : Monotone (thresholdCut t) := by
  intro a b hab
  exact Bool.le_iff_imp.mpr fun ha ↦ decide_eq_true (le_trans (of_decide_eq_true ha) hab)

/-- If every cut is sorted, take the threshold to be the value on the earlier wire. -/
theorem monotone_iff_thresholdCuts (a : ι → α) :
    Monotone a ↔ ∀ t, Monotone (thresholdCut t ∘ a) := by
  constructor
  · intro ha t
    exact (monotone_thresholdCut t).comp ha
  · intro h i j hij
    have hle := Bool.le_iff_imp.mp (h (a i) hij)
    exact of_decide_eq_true (hle (by simp [Function.comp_apply, thresholdCut]))

/-- Boolean correctness implies correctness on any linearly ordered keys for a wire
operation that commutes with threshold cuts. -/
theorem monotone_of_zeroOne {κ : Type*}
    (run : (κ → α) → (ι → α)) (runBits : (κ → Bool) → (ι → Bool))
    (commute : ∀ t a, runBits (thresholdCut t ∘ a) = thresholdCut t ∘ run a)
    (sorted : ∀ bits, Monotone (runBits bits)) (a : κ → α) : Monotone (run a) := by
  apply (monotone_iff_thresholdCuts _).mpr
  intro t
  rw [← commute]
  exact sorted _

end LinearAlgebra.SpectralBooks.Batcher

end OAI
