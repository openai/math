import OAI.Hierarchy.FormulaPartitionKernel
import OAI.Hierarchy.ABPFirstCutCoeffProduct

namespace OAI
/-! # Heavy-child transitions for sums and products of formulas -/

namespace Hierarchy.FormulaPartition

open ABPFirstCut
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V]

/-- Following one child of a sum preserves the current slots. -/
def sumStep (c : F) : Kernel V τ F where
  value _ S T := if S = T then c else 0
  subset := by
    intro a S T h
    by_cases heq : S = T
    · subst T
      exact fun _ h => h
    · simp [heq] at h
  heavy := by
    intro a S T h
    by_cases heq : S = T
    · subst T
      omega
    · simp [heq] at h
  locality := by intros; rfl

/-- A product follows the child with more selected slots, choosing the left
child when both children receive the same number. -/
def productStep (takeLeft : Bool) (sibling : MvPolynomial (Σ i, τ i) F) : Kernel V τ F where
  value a S T := if T ⊆ S ∧ (if takeLeft then (S \ T).card ≤ T.card else (S \ T).card < T.card)
    then slotCoeff a (S \ T) sibling else 0
  subset := by
    intro a S T h
    by_contra hs
    simp [hs] at h
  heavy := by
    intro a S T h
    by_cases hs : T ⊆ S ∧ (if takeLeft then (S \ T).card ≤ T.card else (S \ T).card < T.card)
    · have hcard := Finset.card_sdiff_add_card_eq_card hs.1
      have hcompare := hs.2
      cases takeLeft <;> simp at hcompare <;> omega
    · exact (h (ite_eq_right hs)).elim
  locality := by
    intro a b S T h
    rw [slotCoeff_congr (S \ T) h sibling]

variable [Fintype V]

@[simp] theorem sumStep_act (c : F) (a : ∀ i, τ i) (f : Finset V → F) (S : Finset V) :
    (sumStep c).act a f S = c * f S := by
  classical
  simp [Kernel.act, sumStep, ite_mul]

private theorem productStep_act_powerset (takeLeft : Bool) (sibling : MvPolynomial (Σ i, τ i) F)
    (a : ∀ i, τ i) (f : Finset V → F) (S : Finset V) :
    (productStep takeLeft sibling).act a f S =
      ∑ T ∈ S.powerset, if (if takeLeft then (S \ T).card ≤ T.card else (S \ T).card < T.card)
        then slotCoeff a (S \ T) sibling * f T else 0 := by
  classical
  unfold Kernel.act
  calc
    _ = ∑ T ∈ S.powerset, (productStep takeLeft sibling).value a S T * f T := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro T _ hT
      have hs : ¬ T ⊆ S := fun h => hT (Finset.mem_powerset.mpr h)
      simp [productStep, hs]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro T hT
      simp [productStep, Finset.mem_powerset.mp hT, ite_mul]

omit [Fintype V] in
private theorem sum_powerset_sdiff (S : Finset V) (f : Finset V → F) :
    (∑ T ∈ S.powerset, f (S \ T)) = ∑ T ∈ S.powerset, f T := by
  classical
  apply Finset.sum_nbij' (fun T => S \ T) (fun T => S \ T)
  · exact fun _ _ => Finset.mem_powerset.mpr Finset.sdiff_subset
  · exact fun _ _ => Finset.mem_powerset.mpr Finset.sdiff_subset
  · exact fun _ h => Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp h)
  · exact fun _ h => Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp h)
  · exact fun _ _ => rfl

theorem product_step_eq (a : ∀ i, τ i) (S : Finset V) (p q : MvPolynomial (Σ i, τ i) F) :
    slotCoeff a S (p * q) =
      (productStep true q).act a (fun T => slotCoeff a T p) S +
      (productStep false p).act a (fun T => slotCoeff a T q) S := by
  classical
  rw [slotCoeff_mul, productStep_act_powerset, productStep_act_powerset]
  let right (T : Finset V) := if (S \ T).card < T.card then
    slotCoeff a (S \ T) p * slotCoeff a T q else 0
  change _ = _ + ∑ T ∈ S.powerset, right T
  rw [← sum_powerset_sdiff S right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [right, Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT), ite_true]
  by_cases h : (S \ T).card ≤ T.card
  · simp [h, Nat.not_lt.mpr h, mul_comm]
  · simp [h, Nat.lt_of_not_ge h]

end
end Hierarchy.FormulaPartition

end OAI
