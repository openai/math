import OAI.Computability.VPVNP.HardnessWeights
import OAI.Computability.VPVNP.HardnessWitnessCNF
import OAI.Computability.VPVNP.HardnessWitnessMonomial

/-!
# Eliminating Boolean witness substitutions in a weighted CNF

A selected flag can carry both a scalar and a variable. Its duplicate in the
augmented formula accounts for the variable while the original carries the scalar.
For a witness variable the added implication excludes precisely the assignments
where that variable specializes to zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HardnessWitness

open HardnessCNF
open scoped Classical
variable {k : ℕ} {F : Type*} {X W : Type} [Field F] [Fintype W]

/-- Projection weights on the three blocks of bits. An original flag carries
its scalar, its duplicate carries its formal variable, and the witness is unweighted. -/
noncomputable def augmentedWeight (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) :
    Projection F (Fin (width k W)) X := fun j =>
  Sum.elim (fun i => .inr (a i))
    (Sum.elim (fun i => variableWeight (F := F) (tag i)) (fun _ => .inr 1))
    ((slots k W).symm j)

/-- Reindex a payload assignment by its witness, flags, and copies of the flags. -/
private noncomputable def assignments (k : ℕ) (W : Type) [Fintype W] :
    ((W → Bool) × (Fin k → Bool) × (Fin k → Bool)) ≃ (Fin (width k W) → Bool) where
  toFun s j := Sum.elim s.2.1 (Sum.elim s.2.2 s.1) ((slots k W).symm j)
  invFun z := (fun w => z (slots k W (.inr (.inr w))), fun i => z (slots k W (.inl i)),
    fun i => z (slots k W (.inr (.inl i))))
  left_inv s := by ext <;> simp
  right_inv z := by
    funext j
    obtain ⟨u, rfl⟩ := (slots k W).surjective j
    rcases u with i | i | w <;> simp

private theorem satisfies_assignment (φ : CNF k) (tag : Fin k → Option (X ⊕ W))
    (y : W → Bool) (x z : Fin k → Bool) :
    Satisfies (augment φ tag) (assignments k W (y, x, z)) ↔
      Satisfies φ x ∧ z = x ∧ Compatible tag x y := by
  rw [satisfies_augment]
  simp only [assignments, Equiv.coe_fn_mk, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  rw [funext_iff]

private theorem prod_assignment (a : Fin k → F) (tag : Fin k → Option (X ⊕ W))
    (y : W → Bool) (x z : Fin k → Bool) :
    (∏ i, if assignments k W (y, x, z) i then
        (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1) =
      (∏ i, if x i then MvPolynomial.C (a i) else 1) *
      (∏ i, if z i then (variableWeight (F := F) (tag i)).elim MvPolynomial.X MvPolynomial.C else 1) := by
  classical
  rw [← (slots k W).prod_comp (fun i => if assignments k W (y, x, z) i then
        (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1)]
  have hw : (∏ w : W, if y w then (1 : MvPolynomial X F) else 1) = 1 :=
    Finset.prod_eq_one fun w _ => by cases y w <;> rfl
  simp [Fintype.prod_sum_type, assignments, augmentedWeight]
  erw [hw, mul_one]
  rfl

/-- After summing the Boolean witnesses, a product with one scalar and one
optional variable per selected flag has a CNF presentation with projection weights. -/
theorem sum_witnessValue_weightedCNF (φ : CNF k) (a : Fin k → F) (tag : Fin k → Option (X ⊕ W)) :
    ∑ y : W → Bool, witnessValue y (weightedCNF φ (fun i => monomial (a i) (tag i))) =
      weightedCNF (augment φ tag) (fun i => (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C) := by
  classical
  unfold weightedCNF
  simp only [map_sum, apply_ite, map_zero]
  rw [← (assignments k W).sum_comp (fun b => if Satisfies (augment φ tag) b then
      ∏ i, if b i then (augmentedWeight a tag i).elim MvPolynomial.X MvPolynomial.C else 1 else 0)]
  simp only [Fintype.sum_prod_type, satisfies_assignment, prod_assignment]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_eq_single x]
  · by_cases hs : Satisfies φ x
    · simp only [hs, ite_true, eq_self, true_and, Compatible]
      refine (witnessValue_prod_monomial a tag x y).trans ?_
      congr 1
    · simp [hs]
  · intro z _ hz
    simp [hz]
  · simp

end HardnessWitness

end VPVNP
end Computability
end OAI
