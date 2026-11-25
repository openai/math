import OAI.Hierarchy.GraphVNPPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

namespace OAI
/-! # Total degree of the Boolean-witness polynomial -/

namespace Hierarchy.IncidenceGraph

open MvPolynomial

private theorem totalDegree_prod_le_card_mul {ι σ F : Type*} [Fintype ι] [Field F]
    (f : ι → MvPolynomial σ F) (d : ℕ) (h : ∀ i, (f i).totalDegree ≤ d) :
    (∏ i, f i).totalDegree ≤ Fintype.card ι * d := by
  classical
  calc
    _ ≤ ∑ i, (f i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ _i : ι, d := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

theorem totalDegree_witnessPolynomial_le (G : IncidenceGraph) (F : Type*) [Field F]
    (q b : ℕ) (deg : ∀ v, G.degree v ≤ b) :
    (G.witnessPolynomial F q).totalDegree ≤ Fintype.card G.V * (1 + b * q) := by
  classical
  have hFactor (e : G.E) (a i : Fin q) : (G.labelFactor F q e a i).totalDegree ≤ 1 := by
    unfold labelFactor
    split
    · simp
    · exact (totalDegree_sub _ _).trans (by simp)
  have hSelector (e : G.E) (a : Fin q) : (G.labelSelector F q e a).totalDegree ≤ q := by
    simpa only [labelSelector, Fintype.card_fin, Nat.mul_one] using
      totalDegree_prod_le_card_mul _ 1 (hFactor e a)
  unfold witnessPolynomial
  apply totalDegree_prod_le_card_mul
  intro v
  unfold tablePolynomial
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro t _
  unfold tableTerm
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_X]
  apply Nat.add_le_add_left
  exact (totalDegree_prod_le_card_mul _ q (fun e : G.Incident v => hSelector e.val (t e))).trans
    (Nat.mul_le_mul_right q (deg v))

end Hierarchy.IncidenceGraph

end OAI
