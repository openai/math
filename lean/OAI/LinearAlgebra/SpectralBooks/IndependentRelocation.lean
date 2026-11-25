import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Finset.Piecewise
import Mathlib.Tactic

/-! # Independent endpoint choices in placement interpolation

Successive one-index relocation gives the product-law bound for any finite
set of marked indices. The other indices retain their original placements.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Finset Function

/-- The two-coordinate product law as the four entries of an endpoint table.
The first coordinate indexes rows and the second indexes columns. -/
theorem independent_relocation_two {X Y : Type*} (H : X → Y → ℝ)
    (a b z : X) (c d w : Y) {t u : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hrow : ∀ y, H z y ≤ (1 - t) * H a y + t * H b y)
    (hcol : ∀ x, H x w ≤ (1 - u) * H x c + u * H x d) :
    H z w ≤ (1 - t) * (1 - u) * H a c + (1 - t) * u * H a d +
      t * (1 - u) * H b c + t * u * H b d := by
  calc
    H z w ≤ (1 - t) * H a w + t * H b w := hrow w
    _ ≤ (1 - t) * ((1 - u) * H a c + u * H a d) +
        t * ((1 - u) * H b c + u * H b d) :=
      add_le_add (mul_le_mul_of_nonneg_left (hcol a) (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left (hcol b) ht.1)
    _ = _ := by ring

/-- If each marked coordinate satisfies one-index relocation in every
background placement, the price is bounded by the expected endpoint price
when the marked coordinates make independent Bernoulli choices. The subset
`U` consists of the coordinates placed at their second endpoint. -/
theorem independent_relocation {I X : Type*} [DecidableEq I] (H : (I → X) → ℝ)
    (a b z : I → X) (t : I → ℝ) (s : Finset I) (p : I → X)
    (ht : ∀ i ∈ s, t i ∈ Set.Icc 0 1)
    (hmove : ∀ i ∈ s, ∀ q : I → X, H (update q i (z i)) ≤
      (1 - t i) * H (update q i (a i)) + t i * H (update q i (b i))) :
    H (s.piecewise z p) ≤ ∑ U ∈ s.powerset,
      (∏ i ∈ s, if i ∈ U then t i else 1 - t i) *
        H (s.piecewise (U.piecewise b a) p) := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert i s hi ih =>
    have ht' := fun j (hj : j ∈ s) ↦ ht j (mem_insert_of_mem hj)
    have hmove' := fun j (hj : j ∈ s) ↦ hmove j (mem_insert_of_mem hj)
    rw [piecewise_insert, sum_powerset_insert hi]
    refine (hmove i (mem_insert_self ..) _).trans ?_
    simp only [update_piecewise_of_notMem _ _ _ hi]
    apply (add_le_add
      (mul_le_mul_of_nonneg_left (ih (update p i (a i)) ht' hmove')
        (sub_nonneg.mpr (ht i (mem_insert_self ..)).2))
      (mul_le_mul_of_nonneg_left (ih (update p i (b i)) ht' hmove')
        (ht i (mem_insert_self ..)).1)).trans_eq
    simp only [mul_sum]
    congr 1
    · apply sum_congr rfl
      intro U hU
      have hiU := notMem_mono (mem_powerset.mp hU) hi
      rw [prod_insert hi, ite_eq_right hiU, piecewise_insert,
        U.piecewise_eq_of_notMem b a hiU, update_piecewise_of_notMem _ _ _ hi, mul_assoc]
    · apply sum_congr rfl
      intro U _
      have hprod : (∏ j ∈ s, if j ∈ insert i U then t j else 1 - t j) =
          ∏ j ∈ s, if j ∈ U then t j else 1 - t j := by
        apply prod_congr rfl
        intro j hj
        simp [ne_of_mem_of_not_mem hj hi]
      have hcorner : s.piecewise ((insert i U).piecewise b a) p =
          s.piecewise (U.piecewise b a) p := by
        apply s.piecewise_congr _ (fun _ _ ↦ rfl)
        intro j hj
        exact piecewise_insert_of_ne _ _ _ (ne_of_mem_of_not_mem hj hi)
      rw [prod_insert hi, ite_eq_left (mem_insert_self ..), hprod, piecewise_insert,
        piecewise_insert_self, hcorner, update_piecewise_of_notMem _ _ _ hi, mul_assoc]

/-- The product-law inequality indexed by the Boolean cube of all endpoint choices. -/
theorem independent_relocation_cube {I X : Type*} [Fintype I] [DecidableEq I]
    (H : (I → X) → ℝ) (a b z : I → X) (t : I → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hmove : ∀ i, ∀ q : I → X, H (update q i (z i)) ≤
      (1 - t i) * H (update q i (a i)) + t i * H (update q i (b i))) :
    H z ≤ ∑ e : I → Bool, (∏ i, if e i then t i else 1 - t i) *
      H (fun i ↦ if e i then b i else a i) := by
  classical
  have h := independent_relocation H a b z t univ z (fun i _ ↦ ht i) (fun i _ ↦ hmove i)
  simp only [piecewise_univ, powerset_univ] at h
  let e : Finset I ≃ (I → Bool) :=
    { toFun := fun U i ↦ decide (i ∈ U)
      invFun := fun v ↦ univ.filter fun i ↦ v i
      left_inv := fun U ↦ by ext i; simp
      right_inv := fun v ↦ by ext i; simp }
  exact h.trans_eq (Fintype.sum_equiv e _ _ (fun U ↦ by simp [e]; exact Or.inl rfl))

end SpectralBooks
end LinearAlgebra
end OAI
