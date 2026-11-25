import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.Rat.Defs

/-! # Finite rational word checks

A word of length `k` is enumerated as its `k` letters. The cutoff is strict,
so cutoff zero performs no comparisons. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelAutomatonEquiv

variable {γ : Type*} [Fintype γ]

/-- Compare the two evaluations on every word shorter than `d`. -/
def equalBelow (d : ℕ) (x y : List γ → ℚ) : Bool :=
  decide (∀ k : Fin d, ∀ a : Fin k.val → γ, x (List.ofFn a) = y (List.ofFn a))

theorem equalBelow_iff (d : ℕ) (x y : List γ → ℚ) :
    equalBelow d x y = true ↔ ∀ w : List γ, w.length < d → x w = y w := by
  simp only [equalBelow, decide_eq_true_eq]
  constructor
  · intro h w hw
    simpa using h ⟨w.length, hw⟩ w.get
  · intro h k a
    apply h
    simp

/-- Test the rational series against the identically zero series up to the cutoff. -/
def zeroBelow (d : ℕ) (x : List γ → ℚ) : Bool := equalBelow d x (fun _ => 0)

theorem zeroBelow_iff (d : ℕ) (x : List γ → ℚ) :
    zeroBelow d x = true ↔ ∀ w : List γ, w.length < d → x w = 0 :=
  equalBelow_iff d x _

end KernelAutomatonEquiv

end NearSquareRoot
end Computability
end OAI
