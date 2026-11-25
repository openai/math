import OAI.Computability.BorderVNP.CubeGreedy

/-! # The exact public tie rule for finite coordinate and team scans

The public scan orders finite indices numerically and changes the incumbent
only for a strict improvement. The returned index is smaller than every other
index with the same minimum value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

variable {β : Type*} [LinearOrder β] {n : ℕ}

/-- Characterization of the index returned by the public first-minimum scan,
including ties and a singleton search range. -/
theorem firstMinimum_eq_iff (f : Fin (n+1) → β) (i : Fin (n+1)) :
    firstMinimum f = i ↔ (∀ j, f i ≤ f j) ∧ ∀ j, f j ≤ f i → i ≤ j := by
  have hsome : (List.finRange (n+1)).argmin f ≠ none := by
    intro hn
    have hm := List.mem_finRange i
    rw [List.argmin_eq_none.mp hn] at hm
    contradiction
  have he : firstMinimum f = i ↔ (List.finRange (n+1)).argmin f = some i := by
    unfold firstMinimum
    cases h : (List.finRange (n+1)).argmin f <;> simp_all
  rw [he, List.argmin_eq_some_iff]
  simp only [List.mem_finRange, List.idxOf_finRange, true_implies, true_and]
  rfl

/-- Checking strict improvements before the advertised index and ordinary
minimality afterwards is equivalent to checking the exact first minimizer. -/
theorem firstMinimum_eq_iff_scan (f : Fin (n+1) → β) (i : Fin (n+1)) :
    firstMinimum f = i ↔ (∀ j < i, f i < f j) ∧ ∀ j, i < j → f i ≤ f j := by
  rw [firstMinimum_eq_iff]
  constructor
  · rintro ⟨h,hfirst⟩
    exact ⟨fun j hj => lt_of_not_ge fun hz => hj.not_ge (hfirst j hz), fun j _ => h j⟩
  · rintro ⟨hleft,hright⟩
    constructor
    · intro j
      rcases lt_trichotomy j i with h|rfl|h
      · exact (hleft j h).le
      · rfl
      · exact hright j h
    · intro j hj
      exact le_of_not_gt fun h => (hleft j h).not_ge hj

end Cube

end BorderVNP
end Computability
end OAI
