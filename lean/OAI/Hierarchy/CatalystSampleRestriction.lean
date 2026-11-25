import OAI.Hierarchy.CatalystSliceSum
import OAI.LinearAlgebra.SpectralBooks.Crossing

namespace OAI
/-! # Sampling a single input by local restrictions -/

namespace Hierarchy.Catalyst

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

/-- A tensor obtained by a local projection and a conjunction of local tests is
an ordinary restriction, with an indicator matrix at each site. -/
theorem restriction_of_sample {I : Type*} [Fintype I] {A B : I → Type*}
    [∀ i, Fintype (A i)] {F : Type*} [CommSemiring F]
    (X : ((i : I) → B i) → F) (Y : ((i : I) → A i) → F)
    (project : ∀ i, B i → A i) (G : ∀ i, B i → Prop) (ok : ((i : I) → B i) → Prop)
    [∀ x, Decidable (ok x)] (guard : ∀ x, (∀ i, G i (x i)) ↔ ok x)
    (identity : ∀ x, X x = if ok x then Y (fun i => project i (x i)) else 0) :
    Crossing.IsRestriction X Y := by
  refine ⟨fun i b a => if a = project i b ∧ G i b then (1 : F) else 0, ?_⟩
  intro x
  let sample : (i : I) → A i := fun i => project i (x i)
  have tests (v : (i : I) → A i) :
      (∀ i, v i = project i (x i) ∧ G i (x i)) ↔ v = sample ∧ ok x := by
    constructor
    · intro valid
      exact ⟨funext fun i => (valid i).1, (guard x).1 fun i => (valid i).2⟩
    · rintro ⟨rfl, passed⟩ i
      exact ⟨rfl, (guard x).2 passed i⟩
  exact (identity x).trans (sum_prod_indicator (I := I) (L := A) Y sample
    (fun i a => a = project i (x i) ∧ G i (x i)) (ok x) tests).symm

end Hierarchy.Catalyst

end OAI
