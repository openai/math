import OAI.Computability.VPVNP.PermanentCoefficient
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Coefficient extraction on disjoint variable blocks

When a product has one factor for each block of variables, each choice of monomials
in the factors contributes to a different monomial of the product.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial
open scoped BigOperators

variable {G J V R : Type*} [CommSemiring R]

private theorem blockDegrees_apply [Fintype G] (d : G → J →₀ ℕ) (g : G) (j : J) :
    (∑ i, (d i).mapDomain (Prod.mk i)) (g, j) = d g j := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single g]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective g) _ _
  · intro i _ hi
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨_, he⟩
    exact hi (congrArg Prod.fst he)
  · simp

private theorem blockDegrees_eq_full_iff [Fintype G] [DecidableEq G]
    [Fintype J] [DecidableEq J] (d : G → J →₀ ℕ) :
    (∑ i, (d i).mapDomain (Prod.mk i)) = fullDegree (G × J) ↔ d = fun _ => fullDegree J := by
  constructor
  · intro h
    funext g
    ext j
    simpa only [blockDegrees_apply, fullDegree_apply] using DFunLike.congr_fun h (g, j)
  · rintro rfl
    ext ⟨g, j⟩
    simp only [blockDegrees_apply, fullDegree_apply]

/-- Each block must supply exactly its own squarefree monomial. -/
theorem coeff_fullDegree_prod_rename [Fintype G] [DecidableEq G] [Fintype J] [DecidableEq J]
    (f : G → MvPolynomial J R) :
    (∏ g, rename (Prod.mk g) (f g)).coeff (fullDegree (G × J)) =
      ∏ g, (f g).coeff (fullDegree J) := by
  classical
  have hexp (g : G) : rename (Prod.mk g) (f g) =
      ∑ d ∈ (f g).support, monomial (d.mapDomain (Prod.mk g)) ((f g).coeff d) := by
    conv_lhs => rw [(f g).as_sum, map_sum]
    simp only [rename_monomial]
  simp only [hexp, Finset.prod_univ_sum, prod_monomials, coeff_sum, coeff_monomial,
    blockDegrees_eq_full_iff, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Fintype.mem_piFinset, mem_support_iff, not_forall, not_not] at h
    obtain ⟨g, hg⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ g) hg).symm

/-- Squarefree coefficient extraction across a sum of variable types can be performed
in two steps, first in the left block and then in the right block. -/
theorem coeff_fullDegree_sum [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    (p : MvPolynomial (J ⊕ V) R) :
    p.coeff (fullDegree (J ⊕ V)) =
      ((sumAlgEquiv R J V p).coeff (fullDegree J)).coeff (fullDegree V) := by
  change p.coeff (fullDegree (J ⊕ V)) =
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp p).coeff
      (fullDegree J, fullDegree V)
  rw [AddMonoidAlgebra.coeff_domCongr]
  congr 1
  ext (j | v) <;> simp only [fullDegree_apply, Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppAddEquivProdFinsupp_symm_inr]

end PermanentReduction

end VPVNP
end Computability
end OAI
