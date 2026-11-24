import OAI.Computability.VPVNP.LayerWalk
import OAI.Computability.VPVNP.RegularArcGraph
import OAI.Computability.VPVNP.GraphRounding
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected support of the regular arc multigraph

In the last paragraph of Section 5.3 of *VP and VNP differ over every field*,
the Poincaré inequality for the real line forces connectivity. The multigraph
is specified by its arc multiplicities. Removing loops and identifying
parallel edges leaves the following simple graph, with the same reachability.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V : Type*}

/-- The underlying simple graph of an arc multiplicity matrix. -/
def arcSupportGraph (M : Matrix V V ℕ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun u v ↦ 0 < M u v)

/-- For symmetric multiplicities an edge is present precisely when its
distinct endpoints are joined by an arc. -/
theorem arcSupportGraph_adj (M : Matrix V V ℕ) (hs : ∀ u v, M u v = M v u) (u v : V) :
    (arcSupportGraph M).Adj u v ↔ u ≠ v ∧ 0 < M u v := by
  simp only [arcSupportGraph, SimpleGraph.fromRel_adj, ← hs u v, or_self]

/-- Reachability is unchanged when loops are removed and parallel arcs are
identified. -/
theorem arcSupportGraph_reachable_iff (M : Matrix V V ℕ) (hs : ∀ u v, M u v = M v u)
    (u v : V) : (arcSupportGraph M).Reachable u v ↔
      Relation.ReflTransGen (fun i j ↦ 0 < M i j) u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro path
    exact Relation.ReflTransGen.mono (fun i j h ↦ ((arcSupportGraph_adj M hs i j).mp h).2) u v path
  · intro path
    induction path with
    | refl => exact .refl
    | @tail i j _ hstep ih =>
      by_cases hij : i = j
      · exact hij ▸ ih
      · exact ih.tail ((arcSupportGraph_adj M hs i j).2 ⟨hij, hstep⟩)

/-- Every two vertices of a symmetric arc multigraph with a real Poincaré
bound are joined by a walk in its underlying simple graph. -/
theorem arcSupportGraph_reachable [Fintype V] (M : Matrix V V ℕ) (hs : ∀ u v, M u v = M v u)
    {h : ℕ} {γ : ℝ} (hP : HasPoincareBound ℝ (normalizeArcs M h) γ) (u v : V) :
    (arcSupportGraph M).Reachable u v := by
  apply (arcSupportGraph_reachable_iff M hs u v).mpr
  have hpath := reachable_of_poincare (0 : ℝ) 1 (by norm_num [Real.dist_eq]) _
    (fun i j ↦ by unfold normalizeArcs; positivity)
    (fun i j ↦ by simp only [normalizeArcs, hs i j]) hP u v
  refine Relation.ReflTransGen.mono (fun i j hstep ↦ Nat.pos_of_ne_zero ?_) u v hpath
  intro hz
  simp [normalizeArcs, hz] at hstep

/-- On a nonempty vertex set the real-valued inequality certifies
connectivity in the graph-theoretic sense. -/
theorem arcSupportGraph_connected [Fintype V] [Nonempty V] (M : Matrix V V ℕ)
    (hs : ∀ u v, M u v = M v u) {h : ℕ} {γ : ℝ}
    (hP : HasPoincareBound ℝ (normalizeArcs M h) γ) :
    (arcSupportGraph M).Connected :=
  ⟨arcSupportGraph_reachable M hs hP⟩


/-- The matrix Poincaré inequality, expressed with the paper's averages over
ordered vertex pairs and directed arcs. Parallel edges occur once per port. -/
theorem RegularArcGraph.poincare_on_arcs [Fintype V] [DecidableEq V] {b : ℕ}
    (G : RegularArcGraph V b) {X : Type*} [PseudoMetricSpace X] {γ : ℝ}
    (hP : HasPoincareBound X (normalizeArcs G.multiplicity b) γ) (x : V → X) :
    (∑ u, ∑ v, dist (x u) (x v) ^ 2) / (Fintype.card V : ℝ) ^ 2 ≤
      γ * ((∑ p : V × Fin b, dist (x p.1) (x (G.reverse p).1) ^ 2) /
        ((Fintype.card V : ℝ) * b)) := by
  rw [G.sum_cost (fun u v ↦ dist (x u) (x v) ^ 2)]
  have h := div_le_div_of_nonneg_right (hP x) (Nat.cast_nonneg (Fintype.card V) (α := ℝ))
  rw [div_div, ← pow_two] at h
  refine h.trans_eq ?_
  unfold walkEnergy normalizeArcs
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [mul_div_assoc, div_div, mul_comm (b : ℝ)]
  congr 4
  funext u
  exact Finset.sum_congr rfl fun v _ ↦ by rw [dist_comm]

/-- Lift a symmetric loop-free regular arc matrix to a connected undirected
multigraph without changing any transition multiplicity. -/
theorem exists_connected_regularArcGraph [Fintype V] [Nonempty V] [DecidableEq V]
    (M : Matrix V V ℕ) (hs : ∀ u v, M u v = M v u) {b : ℕ} (hr : ∀ u, ∑ v, M u v = b)
    (hd : ∀ u, M u u = 0) (hreach : ∀ u v, Relation.ReflTransGen (fun i j ↦ 0 < M i j) u v) :
    ∃ G : RegularArcGraph V b, G.multiplicity = M ∧ (arcSupportGraph G.multiplicity).Connected := by
  obtain ⟨G, hG⟩ := exists_regularArcGraph M hs hr hd
  have heq : G.multiplicity = M := funext fun u ↦ funext (hG u)
  refine ⟨G, heq, heq ▸ ?_⟩
  exact ⟨fun u v ↦ (arcSupportGraph_reachable_iff M hs u v).mpr (hreach u v)⟩

end SpectralGeometry

end VPVNP
end Computability
end OAI
