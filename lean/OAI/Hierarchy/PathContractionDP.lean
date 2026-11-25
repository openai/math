import OAI.Hierarchy.ChainProduct
import OAI.Hierarchy.PathTableVars

namespace OAI
/-! # Path contraction by propagation of boundary labels -/

namespace Hierarchy.PathDP
open IncidenceGraph
open scoped BigOperators

noncomputable section

/-- In vertex order, the monomial uses the initial table, a two-edge table for
each interior vertex, and the final table. -/
theorem monomial_eq (F : Type*) [CommSemiring F] (m q : ℕ) (a : Fin (m+1) → Fin q) :
    (path (m+2)).assignmentMonomial F a =
      MvPolynomial.X (left m q (a 0)) *
        (∏ i : Fin m, MvPolynomial.X (middle m q i (a i.castSucc) (a i.succ))) *
        MvPolynomial.X (right m q (a (Fin.last m))) := by
  classical
  change (∏ v : Fin (m+2), (MvPolynomial.X ((path (m+2)).tableIndex a v) :
      MvPolynomial ((path (m+2)).TableVar q) F)) = _
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
  change (MvPolynomial.X ((path (m+2)).tableIndex a (0 : Fin (m+2))) : MvPolynomial ((path (m+2)).TableVar q) F) *
    (∏ i : Fin m, MvPolynomial.X ((path (m+2)).tableIndex a i.succ.castSucc)) *
    MvPolynomial.X ((path (m+2)).tableIndex a (Fin.last (m+1))) = _
  simp only [index_left, index_middle, index_right]

set_option maxHeartbeats 950000 in
/-- Summing the monomials of the graph contraction equals the terminal sum of
the width-`q` recurrence, as an identity of formal polynomials. -/
theorem contraction_eq (F : Type*) [CommSemiring F] (m q : ℕ) :
    (path (m+2)).contraction F q =
      ∑ z : Fin q, ChainProduct.prefixValue m
        (fun x => MvPolynomial.X (left m q x))
        (fun i x y => MvPolynomial.X (middle m q i x y)) z * MvPolynomial.X (right m q z) := by
  classical
  calc
    _ = ∑ a : Fin (m+1) → Fin q, (path (m+2)).assignmentMonomial F a := by
      unfold IncidenceGraph.contraction
      apply Finset.sum_congr
      · apply congrArg (@Finset.univ (Fin (m+1) → Fin q))
        exact Subsingleton.elim _ _
      · intro a _
        rfl
    _ = _ := by
      simp_rw [monomial_eq]
      exact ChainProduct.sum_product_eq (Q := Fin q) (R := MvPolynomial ((path (m+2)).TableVar q) F) m
        (fun x => MvPolynomial.X (left m q x)) (fun i x y => MvPolynomial.X (middle m q i x y))
        (fun x => MvPolynomial.X (right m q x))

end
end Hierarchy.PathDP

end OAI
