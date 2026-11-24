import OAI.Computability.VPVNP.PermanentEquality
import OAI.Computability.VPVNP.PermanentFactors

/-!
# Coefficient of a product of equality gadgets

Each copy has three private columns. Once the incoming port choices have been
fixed, the squarefree coefficient factors across copies. A disagreement in a
single copy makes the entire coefficient vanish.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- All incoming port pairs must agree, and each used pair contributes both
of its exit weights. -/
theorem coeff_portProduct {m : ℕ} (b : R) (hb : -2 * b = 1) (A B : Fin m → R)
    (active picked : Fin m → Bool) :
    ((∏ g, rename (Prod.mk g) (equalityRows b (A g) (B g))) *
      (∏ g, if active g then X (g, (0 : Fin 3)) else 1) *
      (∏ g, if picked g then X (g, (1 : Fin 3)) else 1)).coeff
        (fullDegree (Fin m × Fin 3)) =
      if ∀ g, active g = picked g then ∏ g, if active g then A g * B g else 1 else 0 := by
  let localRows (g : Fin m) : MvPolynomial (Fin 3) R :=
    (if active g then X 0 else 1) * (if picked g then X 1 else 1) * equalityRows b (A g) (B g)
  have hprod :
      (∏ g, rename (Prod.mk g) (equalityRows b (A g) (B g))) *
        (∏ g, if active g then X (g, (0 : Fin 3)) else 1) *
        (∏ g, if picked g then X (g, (1 : Fin 3)) else 1) =
      ∏ g, rename (Prod.mk g) (localRows g) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro g _
    cases ha : active g <;> cases hp : picked g <;> simp [localRows, ha, hp, mul_comm, mul_left_comm, mul_assoc]
  rw [hprod, coeff_fullDegree_prod_rename]
  simp only [localRows, coeff_equalityRows b _ _ hb]
  by_cases h : ∀ g, active g = picked g
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro g _
    rw [h g]
    cases picked g <;> rfl
  · rw [ite_eq_right h]
    obtain ⟨g, hg⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ g)
    cases ha : active g <;> cases hp : picked g <;> simp_all

end PermanentReduction

end VPVNP
end Computability
end OAI
