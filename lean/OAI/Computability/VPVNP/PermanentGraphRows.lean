import OAI.Computability.VPVNP.PermanentGraph

/-!
# Row factors of the exact-one cycle-cover graph

Regard the exterior columns as variables of the coefficient ring. Each occurrence
then supplies its three internal row factors, with the two exits contributing
exterior column variables. Each variable-ring row chooses one of two directions,
and each clause row chooses an occurrence in that clause.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

variable {k m c : ℕ} {R : Type*} [CommRing R]
variable (occ : Fin m → Fin k × Fin c × Bool) (w : Fin k → R) (b : R)

private theorem equalityMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (i j : Fin 3) :
    f (equalityMatrix b i j) = equalityMatrix (f b) i j := by
  fin_cases i <;> fin_cases j <;> simp [equalityMatrix]

private theorem interiorRow (g : Fin m) (i : Fin 3) :
    sumAlgEquiv R (Interior m) (Exterior k m c)
      (∑ v, C (graphMatrix occ w b (.inl (g, i)) v) * X v) =
      rename (Prod.mk g)
        ((∑ j : Fin 3, C (equalityMatrix (C b) i j) * X j) +
          C (![X (ringExit occ g), X (clauseExit occ g), 0] i)) := by
  rw [Fintype.sum_sum_type]
  simp only [map_add, map_sum, map_mul, rename_C, rename_X,
    sumAlgEquiv_X_inl, sumAlgEquiv_X_inr, sumAlgEquiv_C_inl]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [graphMatrix, graphLabels, apply_ite, ite_mul, equalityMatrix_map]
  · fin_cases i <;> simp [graphMatrix, graphLabels, apply_ite, ite_mul]

private theorem ringRow (u : RingRow k m) :
    sumAlgEquiv R (Interior m) (Exterior k m c)
      (∑ v, C (graphMatrix occ w b (.inr (.inl u)) v) * X v) =
      ∑ a : Bool, C (C (ringWeight w u a)) *
        sumAlgEquiv R (Interior m) (Exterior k m c) (X (ringEntry occ u a)) := by
  have e (v : Vertex k m c) :
      graphMatrix occ w b (.inr (.inl u)) v =
        (if v = ringEntry occ u true then ringWeight w u true else 0) +
        (if v = ringEntry occ u false then ringWeight w u false else 0) := by
    by_cases h : v = ringEntry occ u false
    · subst v
      simp [graphMatrix, graphLabels, ringWeight, ringEntry_ne]
    · by_cases ht : v = ringEntry occ u true <;>
        simp [graphMatrix, graphLabels, h, ht, ringWeight, (ringEntry_ne occ u).symm]
  simp only [e, Fintype.sum_bool, map_add, add_mul, Finset.sum_add_distrib, apply_ite C,
    map_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, map_mul,
    sumAlgEquiv_C_inl]

private theorem clauseRow (a : Fin c) :
    sumAlgEquiv R (Interior m) (Exterior k m c)
      (∑ v, C (graphMatrix occ w b (.inr (.inr a)) v) * X v) =
      ∑ g : Fin m, if (occ g).2.1 = a then X (g, 1) else 0 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, map_add, map_sum, map_mul,
    sumAlgEquiv_X_inl, sumAlgEquiv_X_inr, sumAlgEquiv_C_inl]
  simp only [graphMatrix, graphLabels, Sum.elim_inr, id_eq, map_zero, zero_mul, Finset.sum_const_zero,
    add_zero]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : (occ g).2.1 = a <;> simp [hg, apply_ite, ite_mul]

/-- Decomposition into one equality factor per occurrence and one choice factor per
exterior row. The coefficients of the internal polynomials are exterior polynomials. -/
theorem rowProduct_split :
    sumAlgEquiv R (Interior m) (Exterior k m c) (rowProduct (graphMatrix occ w b)) =
      (∏ g, rename (Prod.mk g)
        (equalityRows (C b) (X (ringExit occ g)) (X (clauseExit occ g)))) *
      (∏ u : RingRow k m, ∑ a : Bool, C (C (ringWeight w u a)) *
        sumAlgEquiv R (Interior m) (Exterior k m c) (X (ringEntry occ u a))) *
      (∏ a : Fin c, ∑ g, if (occ g).2.1 = a then X (g, 1) else 0) := by
  rw [rowProduct, map_prod]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, interiorRow, ringRow,
    clauseRow, equalityRows_eq_prod, map_prod, mul_assoc]

end PermanentReduction

end VPVNP
end Computability
end OAI
