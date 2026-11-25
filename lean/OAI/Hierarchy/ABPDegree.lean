import OAI.Hierarchy.Models

namespace OAI
/-! # Total degree of affine branching programs

Each edge raises the degree by at most one. In topological order, the vertex index
bounds the length of every path from the source to that vertex.
-/

namespace Hierarchy

open MvPolynomial
open scoped BigOperators

variable {F : Type*} {σ : Type} [CommSemiring F] [Nontrivial F] [Fintype σ]

theorem Affine.totalDegree_le_one (a : Affine F σ) : a.polynomial.totalDegree ≤ 1 := by
  unfold Affine.polynomial
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul (C (a.coeff i)) (X i)).trans (by simp)

omit [Nontrivial F] [Fintype σ] in
private theorem degree_list_sum {ι : Type*} (f : ι → MvPolynomial σ F)
    (l : List ι) (d : ℕ) (bound : ∀ i, (f i).totalDegree ≤ d) :
    (l.map f).sum.totalDegree ≤ d := by
  induction l with
  | nil => simp
  | cons i l ih =>
    exact (totalDegree_add _ _).trans (max_le (bound i) ih)

theorem Rows.totalDegree_le_index {n : ℕ} (g : Rows F σ n) (i : Fin n) :
    (g.values i).totalDegree ≤ i.val := by
  induction g with
  | source => simp [Rows.values]
  | @snoc n prev edges ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Rows.values, Fin.lastCases_last, Fin.val_last]
      apply degree_list_sum
      intro e
      exact (totalDegree_mul _ _).trans
        ((Nat.add_le_add (ih e.1) e.2.totalDegree_le_one).trans e.1.isLt)
    · simpa [Rows.values] using ih j

/-- The total degree of the formal path sum is bounded by the size of the program. -/
theorem ABP.totalDegree_le_size (g : ABP F σ) : g.polynomial.totalDegree ≤ g.size :=
  (g.rows.totalDegree_le_index g.sink).trans
    (g.sink.isLt.le.trans (Nat.le_add_right _ _))

end Hierarchy

end OAI
