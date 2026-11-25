import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

namespace OAI
/-! # Two independent control workspaces sharing a data assignment

Fixing the data bits separates the two sums over private control bits. The
control coefficients may include a processor, a sorter, or a readout.
-/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open scoped Classical BigOperators

variable {D H₀ H₁ : Type*}

abbrev dataView (z : D ⊕ (H₀ ⊕ H₁) → Bool) (i : D) := z (.inl i)
abbrev zeroView (z : D ⊕ (H₀ ⊕ H₁) → Bool) (i : H₀) := z (.inr (.inl i))
abbrev oneView (z : D ⊕ (H₀ ⊕ H₁) → Bool) (i : H₁) := z (.inr (.inr i))

private theorem split_sum {I J F : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [AddCommMonoid F]
    (f : (I → Bool) → (J → Bool) → F) :
    (∑ z : I ⊕ J → Bool, f (fun i => z (.inl i)) (fun j => z (.inr j))) =
      ∑ x : I → Bool, ∑ y : J → Bool, f x y := by
  rw [← Fintype.sum_prod_type (f := fun t : (I → Bool) × (J → Bool) => f t.1 t.2)]
  apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow I J Bool)
  intro z
  rfl

variable {F : Type*} [Semiring F] [Fintype D] [Fintype H₀] [Fintype H₁]
  [DecidableEq D] [DecidableEq H₀] [DecidableEq H₁]

theorem separate (auth : (D → Bool) → F)
    (pref : (D → Bool) → (H₀ → Bool) → F) (paid : (D → Bool) → (H₁ → Bool) → F) :
    (∑ z : D ⊕ (H₀ ⊕ H₁) → Bool,
      auth (dataView z) * pref (dataView z) (zeroView z) * paid (dataView z) (oneView z)) =
    ∑ x : D → Bool, auth x * (∑ y : H₀ → Bool, pref x y) * (∑ y : H₁ → Bool, paid x y) := by
  calc
    _ = ∑ x : D → Bool, ∑ z : H₀ ⊕ H₁ → Bool,
          auth x * pref x (fun i => z (.inl i)) * paid x (fun j => z (.inr j)) :=
      split_sum (I := D) (J := H₀ ⊕ H₁) (F := F)
        (fun x z => auth x * pref x (fun i => z (.inl i)) * paid x (fun j => z (.inr j)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      refine (split_sum (I := H₀) (J := H₁) (F := F) (fun y z => auth x * pref x y * paid x z)).trans ?_
      simp only [← Finset.mul_sum, ← Finset.sum_mul]

theorem retained (auth : (D → Bool) → F)
    (pref : (D → Bool) → (H₀ → Bool) → F) (paid : (D → Bool) → (H₁ → Bool) → F)
    (admitted : (D → Bool) → Prop) [DecidablePred admitted] (realized : (D → Bool) → F)
    (selector : ∀ x, auth x ≠ 0 → (∑ y : H₀ → Bool, pref x y) = if admitted x then 1 else 0)
    (site : ∀ x, auth x ≠ 0 → admitted x → (∑ y : H₁ → Bool, paid x y) = realized x) :
    (∑ z : D ⊕ (H₀ ⊕ H₁) → Bool,
      auth (dataView z) * pref (dataView z) (zeroView z) * paid (dataView z) (oneView z)) =
    ∑ x : D → Bool, auth x * (if admitted x then 1 else 0) * realized x := by
  rw [separate]
  apply Finset.sum_congr rfl
  intro x _
  by_cases active : auth x = 0
  · simp [active]
  rw [selector x active]
  by_cases keep : admitted x
  · rw [site x active keep]
  · simp [keep]

end Hierarchy.Tagged.WideControlJoin

end
end OAI
