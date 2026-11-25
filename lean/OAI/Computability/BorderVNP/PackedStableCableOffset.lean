import OAI.Computability.BorderVNP.PackedStableOffsets
import OAI.Computability.BorderVNP.PackedDenseNames

/-! # The stable scatter circuit returns the allocator's actual cable offset -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Names

open Crossing Shortening.SeedIntervals PackedHistogram ParseBatchSort
open scoped Classical

variable {D b k w : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (rows : N.Edge ↪ Fin (2^b)) {A : Type} (bin : N.Edge → Option A)

/-- Reordering a sparse descriptor array by its input-dependent bin and stable public row ID,
scanning it, and returning the offsets to public order computes the physical dense allocator.
Holes are free to carry any address bits and have zero width. -/
theorem stableOffset_eq_dense (x : Stable.Input b k w → Bool)
    (fits : ∀ a, bucket (Stable.key x) (Stable.weight x) a < 2^w)
    (width : ∀ e, Stable.weight x (rows e) = N.width e)
    (hole : ∀ u, u ∉ Set.range rows → Stable.weight x u = 0)
    (hkey : ∀ e f, Stable.key x (rows e) = Stable.key x (rows f) ↔ bin e = bin f)
    (e : N.Edge) (a : A) (hi : bin e = some a) :
    value (fun j => (Stable.frame b k w).eval x (rows e,j)) =
      cableOffset (denseLayout N rows) (bin ∘ (denseSlot N rows).symm) a (denseSlot N rows e) := by
  rw [Stable.frame_value x fits, denseOffset]
  symm
  apply Fintype.sum_of_injective rows rows.injective
  · intro u hu
    simp [hole u hu]
  · intro f
    simp only [width, hkey, hi]

end Packing.Names

end BorderVNP
end Computability
end OAI
