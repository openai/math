import Mathlib

open scoped Classical

namespace OAI
namespace Combinatorics
namespace Sunflower

universe u

/-- A family of more than `C ^ k` distinct `k`-sets contains an `r`-sunflower.
The natural base is chosen before the uniformity and ground type. -/
theorem erdosRadoSunflower (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (k : ℕ) (α : Type u) (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
      ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α,
        ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K := by
  sorry

end Sunflower
end Combinatorics
end OAI
