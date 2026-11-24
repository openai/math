import OAI.Computability.VPVNP.SlotGreedyScan
import Mathlib.Data.Fintype.EquivFin

/-!
# Greedy coloring and tag offsets for a finite base

In Appendix C of *VP and VNP differ over every field*, the color and
offset scans apply to any finite base. Choosing enumerations of the
base and tags gives the two existence statements used for wire packing.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.SlotGraph

variable {V : Type*} [Finite V] {d : ℕ} (G : SlotGraph V d)

/-- The two ends of every base arc have distinct colors using `2d + 1`
colors. The bound counts both incoming and outgoing slots. -/
theorem exists_baseColor :
    ∃ color : V → Fin (2 * d + 1), ∀ e, color e.1 ≠ color (G.target e).1 := by
  let := Fintype.ofFinite V
  exact ⟨G.orderedColor (Fintype.equivFin V), G.orderedColor_proper _⟩

/-- The unary and binary conditions on the offsets at all incidences can
be satisfied simultaneously with the indicated tag cardinality. -/
theorem exists_tagOffsets {Tag : Type*} [AddCommGroup Tag] [Fintype Tag] (τ : V × Fin d → Tag)
    (hcard : 2 * d * ((d + 1) + (d + 1) ^ 2) < Fintype.card Tag) :
    ∃ φ : V → Tag, G.ValidTagOffsets τ φ := by
  let := Fintype.ofFinite V
  exact ⟨G.orderedTagOffsets (Fintype.equivFin V) (Fintype.equivFin Tag) τ hcard,
    G.orderedTagOffsets_valid _ _ τ hcard⟩

end Compression.SlotGraph

end VPVNP
end Computability
end OAI
