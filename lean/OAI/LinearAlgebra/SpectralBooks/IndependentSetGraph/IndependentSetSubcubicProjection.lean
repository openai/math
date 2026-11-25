import OAI.LinearAlgebra.SpectralBooks.IndependentSetCubic.IndependentSetCubic
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IndependentSetIncidence
import OAI.LinearAlgebra.SpectralBooks.IndependentSetPadding

/-! # Projection from a prescribed-size bipartite subcubic graph

First split the vertices, then subdivide each edge, and finally pad with isolated
row vertices. All three reductions specialize individual variables to variables
or constants.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace IndependentSetGraph
open scoped Classical

/-- A bipartite graph on precisely `N` vertices and a projection from its
homogeneous independent-set polynomial to `f`. -/
structure GridProjection (R σ : Type*) [CommRing R] (f : MvPolynomial σ R) (N : ℕ) where
  m : ℕ
  k : ℕ
  size_eq : m + k = N
  edge : Fin m → Fin k → Prop
  row_degree : ∀ i, Fintype.card {j // edge i j} ≤ 3
  col_degree : ∀ j, Fintype.card {i // edge i j} ≤ 3
  pin : ((Fin m ⊕ Fin k) × Bool) → ProjectionAtom R σ
  identity : project pin (IndependentSetGrid.polynomial edge) = f

/-- Compose the graph projection with a further variable-or-constant projection. -/
def GridProjection.project {R σ τ : Type*} [CommRing R] {f : MvPolynomial σ R} {N : ℕ}
    (G : GridProjection R σ f N) (q : σ → ProjectionAtom R τ) :
    GridProjection R τ (IndependentSetGraph.project q f) N where
  m := G.m
  k := G.k
  size_eq := G.size_eq
  edge := G.edge
  row_degree := G.row_degree
  col_degree := G.col_degree
  pin i := (G.pin i).elim q Sum.inr
  identity := by rw [← project_comp, G.identity]

private theorem padded_row_degree {m k : ℕ} (G : Fin m → Fin k → Prop) (t : ℕ)
    (h : ∀ i, Fintype.card {j // G i j} ≤ 3) (i : Fin (m+t)) :
    Fintype.card {j // IndependentSetGrid.padded G t i j} ≤ 3 := by
  induction i using Fin.addCases with
  | left i => simpa [IndependentSetGrid.padded] using h i
  | right i => simp [IndependentSetGrid.padded]

private theorem padded_column_degree {m k : ℕ} (G : Fin m → Fin k → Prop) (t : ℕ)
    (h : ∀ j, Fintype.card {i // G i j} ≤ 3) (j : Fin k) :
    Fintype.card {i // IndependentSetGrid.padded G t i j} ≤ 3 := by
  let f : {i // G i j} → {i // IndependentSetGrid.padded G t i j} :=
    fun i => ⟨i.val.castAdd t, by simpa [IndependentSetGrid.padded] using i.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact ⟨⟨i, by simpa [IndependentSetGrid.padded] using hi⟩, rfl⟩
    | right i => simp [IndependentSetGrid.padded] at hi
  exact (Fintype.card_le_of_surjective f hf).trans (h j)

/-- Every finite graph's independent-set polynomial is a projection of that of
a bipartite graph of degree at most three, at every size at least `|V| + 25|E|`. -/
theorem exists_gridProjection_of_polynomial {R V E : Type*} [CommRing R] [Fintype V] [Fintype E]
    (l r : E → V) {N : ℕ} (hN : Fintype.card V + 25 * Fintype.card E ≤ N) :
    Nonempty (GridProjection R (V × Bool) (polynomial R l r) N) := by
  let a := Fintype.card (IndependentSetCubic.Vertex l r)
  let b := Fintype.card (IndependentSetCubic.Edge l r)
  let t := N - (a + b)
  let G := numberedIncidence (IndependentSetCubic.left l r) (IndependentSetCubic.right l r)
  have hab : a + b = Fintype.card V + 25 * Fintype.card E := by
    dsimp only [a, b]
    rw [IndependentSetCubic.card_vertex, IndependentSetCubic.card_edge]
    omega
  let p := IndependentSetGrid.paddingProjection (R := R) a b t
  let q := numberedProjection (R := R) (V := IndependentSetCubic.Vertex l r)
    (E := IndependentSetCubic.Edge l r)
  let s := IndependentSetCubic.projection (R := R) l r
  refine ⟨{ m := a + t, k := b, size_eq := by dsimp [t]; omega
            edge := IndependentSetGrid.padded G t
            row_degree := padded_row_degree G t
              (row_degree_le _ _ 3 (fun v => by
                simpa only [← Nat.card_eq_fintype_card] using IndependentSetCubic.degree_le_three l r v))
            col_degree := padded_column_degree G t fun j => (column_degree_le _ _ j).trans (by decide)
            pin := fun i => ((p i).elim q Sum.inr).elim s Sum.inr
            identity := ?_ }⟩
  rw [← project_comp, ← project_comp]
  rw [show project p (IndependentSetGrid.polynomial (IndependentSetGrid.padded G t)) =
      IndependentSetGrid.polynomial G from IndependentSetGrid.project_padded_polynomial G t]
  rw [show project q (IndependentSetGrid.polynomial G) = _ from project_numbered_polynomial _ _]
  exact IndependentSetCubic.project_polynomial l r

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
