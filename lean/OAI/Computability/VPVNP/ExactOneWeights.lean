import OAI.Computability.VPVNP.ExactOneSolutions
import OAI.Computability.VPVNP.HardnessWeights

/-!
# Weighted exact-one reduction

The original variables retain their weights. Every selector and filler has
weight one, so the unique extension of an assignment preserves its contribution
over any commutative semiring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ExactOne

open HardnessCNF MvPolynomial
open scoped Classical

variable {k : ℕ} {R : Type*}

/-- Weighted generating function of assignments meeting each clause exactly once. -/
noncomputable def weightedExactOne [CommSemiring R] (φ : CNF k) (w : Fin k → R) : R :=
  ∑ x, if Holds φ x then ∏ i, if x i then w i else 1 else 0

/-- A selector or filler receives the supplied neutral label. -/
private noncomputable def extendLabels {A : Type*} (φ : CNF k) (w : Fin k → A) (neutral : A)
    (i : Fin (width φ)) : A :=
  ((index φ).symm i).elim w (fun _ => neutral)

/-- Extend the weights to all Boolean variables of the exact-one instance. -/
noncomputable def augmentWeight [One R] (φ : CNF k) (w : Fin k → R) : Fin (width φ) → R :=
  extendLabels φ w 1

/-- The extension also preserves variable-or-constant projection labels. -/
noncomputable def augmentProjection {τ : Type*} [One R] (φ : CNF k)
    (w : Projection R (Fin k) τ) : Projection R (Fin (width φ)) τ :=
  extendLabels φ w (.inr 1)

theorem augmentProjection_eval {τ : Type*} [CommSemiring R] (φ : CNF k)
    (w : Projection R (Fin k) τ) (i : Fin (width φ)) :
    (augmentProjection φ w i).elim X C = augmentWeight φ (fun j => (w j).elim X C) i := by
  obtain ⟨s, rfl⟩ := (index φ).surjective i
  cases s <;> simp [augmentProjection, augmentWeight, extendLabels]

private theorem product_augmentWeight [CommSemiring R] (φ : CNF k)
    (w : Fin k → R) (x : Fin (width φ) → Bool) :
    (∏ i, if x i then augmentWeight φ w i else 1) =
      ∏ j, if original φ x j then w j else 1 := by
  rw [← (index φ).prod_comp (fun i => if x i then augmentWeight φ w i else 1),
    Fintype.prod_sum_type]
  simp [augmentWeight, extendLabels, original, data]
  rfl

theorem weightedExactOne_eq_sum [CommSemiring R] (φ : CNF k) (w : Fin k → R) :
    weightedExactOne φ w =
      ∑ x : {x : Fin k → Bool // Holds φ x}, ∏ i, if x.val i then w i else 1 := by
  rw [weightedExactOne, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The exact-one reduction preserves the entire generating polynomial. -/
theorem weightedExactOne_augment [CommSemiring R] (φ : CNF k) (w : Fin k → R) :
    weightedExactOne (augment φ) (augmentWeight φ w) = weightedCNF φ w := by
  have hcnf : weightedCNF φ w =
      ∑ y : {y : Fin k → Bool // Satisfies φ y}, ∏ j, if y.val j then w j else 1 := by
    rw [weightedCNF, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [weightedExactOne_eq_sum, hcnf]
  rw [← (solutionsEquiv φ).sum_comp (fun y => ∏ j, if y.val j then w j else 1)]
  exact Finset.sum_congr rfl fun x _ => product_augmentWeight φ w x.val

end ExactOne

end VPVNP
end Computability
end OAI
