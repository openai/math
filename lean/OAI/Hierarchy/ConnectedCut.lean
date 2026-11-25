import OAI.Hierarchy.GraphCutFamily
import OAI.Hierarchy.PathWitness

namespace OAI
/-! # Every nontrivial block of a connected graph cuts an edge -/

namespace Hierarchy.IncidenceGraph

open scoped Classical

theorem mem_iff_of_boundary_empty (G : IncidenceGraph) (S : Finset G.V)
    (empty : G.boundaryEdges S = ∅) {u v : G.V} (path : G.Connected u v) :
    u ∈ S ↔ v ∈ S := by
  classical
  have step {a b : G.V} (adj : G.Adjacent a b) : a ∈ S ↔ b ∈ S := by
    obtain ⟨e, h⟩ := adj
    have equal : G.left e ∈ S ↔ G.right e ∈ S := by
      by_contra h
      have he : e ∈ G.boundaryEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      simp [empty] at he
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact equal
    · exact equal.symm
  induction path with
  | refl => rfl
  | tail p h ih => exact ih.trans (step h)

theorem boundary_nonempty_of_connected (G : IncidenceGraph) (S : Finset G.V)
    {u v : G.V} (path : G.Connected u v) (inside : u ∈ S) (outside : v ∉ S) :
    (G.boundaryEdges S).Nonempty := by
  classical
  apply Finset.nonempty_iff_ne_empty.mpr
  exact fun empty => outside ((G.mem_iff_of_boundary_empty S empty path).mp inside)

theorem boundary_nonempty_of_block (G : IncidenceGraph)
    (connected : ∀ u v, G.Connected u v) {J : Type*} [Nontrivial J]
    (block : G.V → J) (onto : Function.Surjective block) (j : J) :
    (G.boundaryEdges (Finset.univ.filter fun v => block v = j)).Nonempty := by
  classical
  obtain ⟨other, distinct⟩ := exists_ne j
  obtain ⟨u, hu⟩ := onto j
  obtain ⟨v, hv⟩ := onto other
  exact G.boundary_nonempty_of_connected _ (connected u v) (by simpa using hu)
    (by simpa [hv] using distinct)

theorem path_block_boundary (n : ℕ) {J : Type*} [Nontrivial J]
    (block : (path n).V → J) (onto : Function.Surjective block) (j : J) :
    ((path n).boundaryEdges (Finset.univ.filter fun v => block v = j)).Nonempty :=
  (path n).boundary_nonempty_of_block (path_connected n) block onto j

end Hierarchy.IncidenceGraph

end OAI
