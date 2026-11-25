import OAI.Hierarchy.DecompositionLines
import OAI.Hierarchy.GridGraph

namespace OAI
/-! # The square grid has unbounded treewidth

In a tree decomposition, a row and a column meet in a bag containing their common
vertex. One bag therefore hits every row or every column, and contains at least
as many distinct vertices as the side length of the grid.
-/

namespace Hierarchy.SquareGrid

open IncidenceGraph
open scoped Classical

/-- A bag whose projection hits every index has at least as many vertices as indices. -/
private theorem card_of_hits {α : Type} {n : ℕ} (s : Finset α) (coordinate : α → Fin n)
    (hits : ∀ a, ∃ x ∈ s, coordinate x = a) : n ≤ s.card := by
  have onto : Function.Surjective (fun x : ↥s => coordinate x.val) := by
    intro a
    obtain ⟨x,hx,ha⟩ := hits a
    exact ⟨⟨x,hx⟩,ha⟩
  simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_le_of_surjective _ onto

/-- Every tree decomposition of an `n × n` grid has a bag containing at least `n` vertices. -/
theorem large_bag (n : ℕ) (D : (graph n).TreeDecomposition) :
    ∃ i, n ≤ (D.bag i).card := by
  cases n with
  | zero => exact ⟨D.root,Nat.zero_le _⟩
  | succ k =>
    let row (r : Fin (k+1)) (i : D.Bag) : Prop := ∃ c : Fin (k+1), (r,c) ∈ D.bag i
    let col (c : Fin (k+1)) (i : D.Bag) : Prop := ∃ r : Fin (k+1), (r,c) ∈ D.bag i
    have rowPath (r : Fin (k+1)) : ∃ top, D.RootedRegion (row r) top :=
      D.path_region (fun c => (r,c)) (row_adj r)
    have colPath (c : Fin (k+1)) : ∃ top, D.RootedRegion (col c) top :=
      D.path_region (fun r => (r,c)) (col_adj c)
    have meet (r c : Fin (k+1)) : ∃ i, row r i ∧ col c i := by
      obtain ⟨i,hi⟩ := D.vertex_cover (r,c)
      exact ⟨i,⟨c,hi⟩,r,hi⟩
    obtain ⟨i,allRows|allCols⟩ := D.rectangular_bag row col rowPath colPath meet
    · refine ⟨i,card_of_hits (D.bag i) Prod.fst ?_⟩
      intro r
      obtain ⟨c,hc⟩ := allRows r
      exact ⟨(r,c),hc,rfl⟩
    · refine ⟨i,card_of_hits (D.bag i) Prod.snd ?_⟩
      intro c
      obtain ⟨r,hr⟩ := allCols c
      exact ⟨(r,c),hr,rfl⟩

theorem width_lower {n b : ℕ} (h : (graph n).TreewidthAtMost b) : n ≤ b+1 := by
  obtain ⟨D, cap⟩ := h
  obtain ⟨i,hi⟩ := large_bag n D
  exact hi.trans (cap i)

theorem unbounded_treewidth : ¬ ∃ b, ∀ n, (graph n).TreewidthAtMost b := by
  rintro ⟨b,cap⟩
  have := width_lower (cap (b+2))
  omega

theorem bounded_degree : ∃ b, ∀ n (v : (graph n).V), (graph n).degree v ≤ b :=
  ⟨4,degree_le_four⟩

theorem polynomial_order : Computability.VPVNP.PolynomiallyBounded (fun n => Fintype.card (graph n).V) := by
  refine ⟨1,2,0,fun n _ => ?_⟩
  change Fintype.card (graph n).V ≤ 1 * n^2
  rw [card_vertices, one_mul]


end Hierarchy.SquareGrid

end OAI
