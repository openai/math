import OAI.Computability.VPVNP.PermanentPadding
import OAI.Computability.VPVNP.PermanentGraph

/-!
# Literal projections of the generic permanent

A weighted directed graph whose edges carry constants or variables gives a
projection of the permanent. A simultaneous reindexing of both matrix axes
lets us use any finite vertex type.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial

/-- Relabeling the vertices bijectively preserves all cycle-cover weights. -/
theorem permanent_submatrix_equiv_self {I J R : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [CommSemiring R] (e : I ≃ J) (M : Matrix J J R) :
    (M.submatrix e e).permanent = M.permanent := by
  unfold Matrix.permanent
  apply Fintype.sum_equiv (Equiv.permCongr e)
  intro π
  apply Fintype.prod_equiv e
  intro i
  simp

/-- A finite matrix with literal labels is obtained by a projection of the
generic square matrix of the same order. -/
theorem exists_permanent_label_projection {V σ F : Type*} [Fintype V] [DecidableEq V]
    [CommSemiring F] {n : ℕ} (hn : Fintype.card V = n) (label : V → V → σ ⊕ F) :
    ∃ φ : Projection F (Fin n × Fin n) σ, φ.hom (permanentPolynomial F n) =
      (Matrix.of fun i j => (label i j).elim X C).permanent := by
  let e := (Fintype.equivFinOfCardEq hn).symm
  let φ : Projection F (Fin n × Fin n) σ := fun ij => label (e ij.1) (e ij.2)
  refine ⟨φ, ?_⟩
  let M : Matrix V V (MvPolynomial σ F) := Matrix.of fun i j => (label i j).elim X C
  calc
    φ.hom (permanentPolynomial F n) = (M.submatrix e e).permanent := by
      simp [permanentPolynomial, Matrix.permanent, Projection.hom, φ, M]
    _ = M.permanent := permanent_submatrix_equiv_self e M

variable {k m c : ℕ}

private theorem map_equalityMatrix {F R : Type*} [CommRing F] [CommRing R] (h : F →+* R)
    (b : F) (i j : Fin 3) : h (equalityMatrix b i j) = equalityMatrix (h b) i j := by
  fin_cases i <;> fin_cases j <;> simp [equalityMatrix]

private theorem map_ringLabel {F R : Type*} [CommRing F] [CommRing R] (h : F →+* R)
    (u : RingRow k m) (a : Bool) :
    (ringLabel (F := F) u a).map id h = ringLabel u a := by
  unfold ringLabel
  split <;> simp

/-- Scalar specialization of the graph acts entrywise on its scalar labels. -/
theorem map_graphLabels {F R : Type*} [CommRing F] [CommRing R] (h : F →+* R)
    (occ : Fin m → Fin k × Fin c × Bool) (b : F) (u v : Vertex k m c) :
    (graphLabels occ b u v).map id h = graphLabels occ (h b) u v := by
  rcases u with ⟨g, i⟩ | (x | a)
  · rcases v with ⟨g', j⟩ | y
    · simp [graphLabels, apply_ite h, map_equalityMatrix]
    · simp [graphLabels, apply_ite h]
  · simp only [graphLabels]
    split
    · exact map_ringLabel h x false
    · split
      · exact map_ringLabel h x true
      · simp
  · rcases v with ⟨g, j⟩ | y <;> simp [graphLabels, apply_ite h]

theorem card_graphVertex (k m c : ℕ) :
    Fintype.card (Vertex k m c) = 3 * m + k * (m + 2) + c := by
  simp only [Vertex, Interior, Exterior, RingRow, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  omega

/-- Reindex the gadget graph and use each entry as a literal variable or constant
of the generic permanent. This uses exactly three internal vertices per occurrence,
one ring of length `m + 2` per variable, and one vertex per clause. -/
theorem weightedLabelsProjection {F σ : Type*} [CommRing F]
    (occ : Fin m → Fin k × Fin c × Bool) (w : Projection F (Fin k) σ) (b : F) :
    ∃ φ : Projection F
        (Fin (3 * m + k * (m + 2) + c) × Fin (3 * m + k * (m + 2) + c)) σ,
      φ.hom (permanentPolynomial F (3 * m + k * (m + 2) + c)) =
        (graphMatrix occ (fun i => (w i).elim X C) (C b)).permanent := by
  let label (u v : Vertex k m c) : σ ⊕ F := (graphLabels occ b u v).elim w Sum.inr
  obtain ⟨φ, hp⟩ := exists_permanent_label_projection (card_graphVertex k m c) label
  refine ⟨φ, hp.trans ?_⟩
  congr 1
  ext u v
  simp only [Matrix.of_apply, graphMatrix, ← map_graphLabels (C : F →+* MvPolynomial σ F),
    label]
  cases graphLabels occ b u v <;> rfl

end PermanentReduction

end VPVNP
end Computability
end OAI
