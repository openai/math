import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Finite indicator sums for a prescribed family of wire inputs -/

namespace Hierarchy.Catalyst

open scoped BigOperators

/-- A product of local indicator functions selects the designated input precisely
when the test on its output holds. -/
theorem sum_prod_indicator {I : Type*} [Fintype I] [DecidableEq I]
    {L : I → Type*} [∀ i, Fintype (L i)] {F : Type*} [CommSemiring F]
    (w : ((i : I) → L i) → F) (c : (i : I) → L i)
    (T : (i : I) → L i → Prop) [∀ i x, Decidable (T i x)]
    (ok : Prop) [Decidable ok] (tests : ∀ v, (∀ i, T i (v i)) ↔ v = c ∧ ok) :
    (∑ v : (i : I) → L i, w v * ∏ i, if T i (v i) then (1 : F) else 0) =
      if ok then w c else 0 := by
  classical
  have dead (v : (i : I) → L i) (reject : ¬∀ i, T i (v i)) :
      (∏ i, if T i (v i) then (1 : F) else 0) = 0 := by
    obtain ⟨i, hi⟩ := not_forall.mp reject
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  by_cases accept : ok
  · rw [ite_eq_left accept, Finset.sum_eq_single c]
    · simp [(tests c).2 ⟨rfl, accept⟩]
    · intro v _ ne
      rw [dead v (fun all => ne ((tests v).1 all).1), mul_zero]
    · simp
  · rw [ite_eq_right accept]
    apply Finset.sum_eq_zero
    intro v _
    rw [dead v (fun all => accept ((tests v).1 all).2), mul_zero]

end Hierarchy.Catalyst

end OAI
