import OAI.Hierarchy.DecompositionSubtree
import Mathlib.Data.Finset.Max

namespace OAI
/-! # Paths and intersecting rows and columns in a tree decomposition -/

namespace Hierarchy.IncidenceGraph.TreeDecomposition

variable {G : IncidenceGraph} (D : G.TreeDecomposition)

private theorem adjacent_bag {u v : G.V} (h : G.Adjacent u v) :
    ∃ i, u ∈ D.bag i ∧ v ∈ D.bag i := by
  obtain ⟨e, endpoints⟩ := h
  obtain ⟨i,hl,hr⟩ := D.edge_cover e
  rcases endpoints with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨i,hl,hr⟩
  · exact ⟨i,hr,hl⟩

/-- The bags meeting a nonempty graph path form a rooted region. -/
theorem path_region {n : ℕ} (v : Fin (n+1) → G.V)
    (path : ∀ t : Fin n, G.Adjacent (v t.castSucc) (v t.succ)) :
    ∃ top, D.RootedRegion (fun i => ∃ j, v j ∈ D.bag i) top := by
  induction n with
  | zero =>
    obtain ⟨a,ha⟩ := D.running (v 0)
    refine ⟨a,?_⟩
    have single : (fun i => ∃ j, v j ∈ D.bag i) = (fun i => v 0 ∈ D.bag i) := by
      funext i
      exact propext Fin.exists_fin_one
    rw [single]
    exact ha
  | succ n ih =>
    obtain ⟨a,ha⟩ := D.running (v 0)
    obtain ⟨b,hb⟩ := ih (fun j => v j.succ) (fun t => path t.succ)
    obtain ⟨i,first,second⟩ := D.adjacent_bag (path 0)
    have meet : ∃ i, v 0 ∈ D.bag i ∧ ∃ j : Fin (n+1), v j.succ ∈ D.bag i :=
      ⟨i,first,0,second⟩
    have eqn : (fun i => ∃ j, v j ∈ D.bag i) =
        (fun i => v 0 ∈ D.bag i ∨ ∃ j : Fin (n+1), v j.succ ∈ D.bag i) := by
      funext i
      exact propext Fin.exists_fin_succ
    rw [eqn]
    exact D.region_union (a:=a) (b:=b)
      (show D.RootedRegion (fun i => v 0 ∈ D.bag i) a from ha) hb meet

/-- If each row meets every column, a bag contains a point of every row
or a point of every column. -/
theorem rectangular_bag {n : ℕ} [NeZero n] (row col : Fin n → D.Bag → Prop)
    (hrow : ∀ a, ∃ top, D.RootedRegion (row a) top)
    (hcol : ∀ b, ∃ top, D.RootedRegion (col b) top)
    (overlap : ∀ a b, ∃ i, row a i ∧ col b i) :
    ∃ i, (∀ a, row a i) ∨ (∀ b, col b i) := by
  classical
  choose r hr using hrow
  choose c hc using hcol
  have nonempty : (Finset.univ : Finset (Fin n)).Nonempty := ⟨0, Finset.mem_univ _⟩
  obtain ⟨a, _, hmaxRow⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun x => D.level (r x)) nonempty
  obtain ⟨b, _, hmaxCol⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun x => D.level (c x)) nonempty
  rcases le_total (D.level (r a)) (D.level (c b)) with h | h
  · refine ⟨c b, Or.inl (fun x => ?_)⟩
    exact D.region_intersection (hr x) (hc b) (overlap x b)
      ((hmaxRow x (Finset.mem_univ x)).trans h)
  · refine ⟨r a, Or.inr (fun y => ?_)⟩
    obtain ⟨i, hi, hj⟩ := overlap a y
    exact D.region_intersection (hc y) (hr a) ⟨i, hj, hi⟩
      ((hmaxCol y (Finset.mem_univ y)).trans h)


end Hierarchy.IncidenceGraph.TreeDecomposition

end OAI
