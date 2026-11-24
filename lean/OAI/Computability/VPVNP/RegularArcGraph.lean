import OAI.Computability.VPVNP.PortMatching
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Loop-free regular multigraphs represented by paired arcs

Theorem 5.1 counts the oriented arcs of a multigraph, with equal
multiplicities in both directions. Each vertex has one arc per port.
Reversal pairs the arcs at opposite ends of each undirected edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

/-- A loop-free undirected multigraph with exactly `b` outgoing arcs at each vertex. -/
structure RegularArcGraph (V : Type*) (b : ℕ) where
  /-- Involutive permutation pairing each outgoing port with the oppositely oriented port of
  the same undirected edge. -/
  reverse : Equiv.Perm (V × Fin b)
  involutive : Function.Involutive reverse
  ends_ne : ∀ p, (reverse p).1 ≠ p.1

namespace RegularArcGraph

variable {V : Type*} {b : ℕ} (G : RegularArcGraph V b)

/-- Number of arcs going from `u` to `v`. -/
def multiplicity [DecidableEq V] (u v : V) : ℕ :=
  (Finset.univ.filter (fun k : Fin b ↦ (G.reverse (u, k)).1 = v)).card

/-- Positive multiplicity is equivalent to the existence of a port leading to the vertex. -/
theorem multiplicity_pos_iff [DecidableEq V] (u v : V) :
    0 < G.multiplicity u v ↔ ∃ k : Fin b, (G.reverse (u, k)).1 = v := by
  simp [multiplicity, Finset.card_pos, Finset.Nonempty]

/-- Loop-freeness gives zero diagonal in the multiplicity matrix. -/
@[simp] theorem multiplicity_self [DecidableEq V] (u : V) : G.multiplicity u u = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [G.multiplicity_pos_iff]
  exact fun ⟨k, hk⟩ ↦ G.ends_ne (u, k) hk

/-- Reversal gives a bijection between the arcs of the two orientations. -/
theorem multiplicity_symmetric [DecidableEq V] (u v : V) :
    G.multiplicity u v = G.multiplicity v u := by
  have back (x y : V) (k : Fin b) (h : (G.reverse (x, k)).1 = y) :
      G.reverse (y, (G.reverse (x, k)).2) = (x, k) := by
    subst y
    exact G.involutive (x, k)
  apply Finset.card_nbij' (fun k ↦ (G.reverse (u, k)).2) (fun l ↦ (G.reverse (v, l)).2)
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst
      (back u v k (Finset.mem_filter.mp hk).2)⟩
  · intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg Prod.fst
      (back v u k (Finset.mem_filter.mp hk).2)⟩
  · intro k hk
    exact congrArg Prod.snd (back u v k (Finset.mem_filter.mp hk).2)
  · intro k hk
    exact congrArg Prod.snd (back v u k (Finset.mem_filter.mp hk).2)

/-- Counting the outgoing ports gives the degree at every vertex. -/
theorem degree [Fintype V] [DecidableEq V] (u : V) : ∑ v, G.multiplicity u v = b := by
  simpa [multiplicity] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin b)) Finset.univ (fun k ↦ (G.reverse (u, k)).1)

/-- Reversal exchanges the two different arcs of each edge. -/
theorem reverse_ne (p : V × Fin b) : G.reverse p ≠ p :=
  fun he ↦ G.ends_ne p (congrArg Prod.fst he)

/-- Group the sum of any arc cost by its ordered pair of endpoints. -/
theorem sum_cost [Fintype V] [DecidableEq V] (c : V → V → ℝ) :
    (∑ p : V × Fin b, c p.1 (G.reverse p).1) = ∑ u, ∑ v, (G.multiplicity u v : ℝ) * c u v := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  have term (v : V) : (G.multiplicity u v : ℝ) * c u v =
      ∑ k : Fin b, if (G.reverse (u, k)).1 = v then c u v else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, multiplicity]
  simp_rw [term]
  rw [Finset.sum_comm]
  simp

end RegularArcGraph

/-- Realize a symmetric zero-diagonal matrix with constant row sum by a regular graph. -/
theorem exists_regularArcGraph {V : Type*} [Fintype V] [DecidableEq V] {b : ℕ}
    (M : V → V → ℕ) (hsym : ∀ u v, M u v = M v u) (hrow : ∀ u, ∑ v, M u v = b)
    (hdiag : ∀ u, M u u = 0) :
    ∃ G : RegularArcGraph V b, ∀ u v, G.multiplicity u v = M u v := by
  obtain ⟨σ, hσ, hcount, _⟩ := exists_portMatching M hsym hrow
  refine ⟨⟨σ, hσ, ?_⟩, hcount⟩
  rintro ⟨u, k⟩ hk
  have hempty : (Finset.univ.filter (fun l : Fin b ↦ (σ (u, l)).1 = u)) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact (hcount u u).trans (hdiag u)
  have hmem : k ∈ Finset.univ.filter (fun l : Fin b ↦ (σ (u, l)).1 = u) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  simp only [hempty, Finset.notMem_empty] at hmem

end SpectralGeometry

end VPVNP
end Computability
end OAI
