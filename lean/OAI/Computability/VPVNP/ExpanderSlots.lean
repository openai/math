import OAI.Computability.VPVNP.RegularArcGraph
import OAI.Computability.VPVNP.SlotGraph

/-!
# Numbering the arcs of a regular expander

The graph supplied by Theorem 5.1 has paired arcs. The wire construction
uses one outgoing and one incoming slot for each arc. At the destination
we use the outgoing number of its reverse as the incoming slot number.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {V : Type*} {d : ℕ}

/-- Use paired arcs as the outgoing and incoming slots of a directed graph. -/
def RegularArcGraph.toSlotGraph (G : RegularArcGraph V d) : Compression.SlotGraph V d :=
  ⟨G.reverse, G.ends_ne⟩

/-- A loop-free symmetric multiplicity matrix with constant degree admits a
slot numbering with exactly its specified arc counts. -/
theorem exists_expanderSlots [Fintype V] [DecidableEq V] (M : V → V → ℕ)
    (hsym : ∀ u v, M u v = M v u) (hrow : ∀ u, ∑ v, M u v = d) (hdiag : ∀ u, M u u = 0) :
    ∃ H : Compression.SlotGraph V d, ∀ u v,
      (Finset.univ.filter (fun h : Fin d ↦ (H.target (u, h)).1 = v)).card = M u v := by
  obtain ⟨G, hG⟩ := exists_regularArcGraph M hsym hrow hdiag
  exact ⟨G.toSlotGraph, hG⟩

end SpectralGeometry

namespace Compression.SlotGraph

/-- Group a sum over the outgoing slots of a vertex by destination. This
also applies when the cost depends on the source, by fixing the source. -/
theorem sum_outgoing {V A : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid A] {d : ℕ}
    (H : SlotGraph V d) (M : V → V → ℕ)
    (hcount : ∀ u v, (Finset.univ.filter (fun h : Fin d ↦ (H.target (u, h)).1 = v)).card = M u v)
    (u : V) (cost : V → A) :
    ∑ h : Fin d, cost (H.target (u, h)).1 = ∑ v, M u v • cost v := by
  simpa only [Finset.sum_const, hcount] using
    (Finset.sum_fiberwise' Finset.univ (fun h : Fin d ↦ (H.target (u, h)).1) cost).symm

end Compression.SlotGraph

end VPVNP
end Computability
end OAI
