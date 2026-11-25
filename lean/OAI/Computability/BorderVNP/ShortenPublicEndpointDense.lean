import OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics
import OAI.Computability.BorderVNP.PackedDenseNames

/-!
# Reading the sparse endpoint table in the densely numbered physical layout

Each physical cable queries the stable number of its original edge. Its dense
rank governs allocator order while the lookup table keeps the sparse public rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicEndpoints

open Crossing Packing.Names ParseBatchSort

variable {D S E k w : ℕ} {P B : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (site : N.Site ↪ Fin S) (rows : N.Edge ↪ Fin E) (dummy : Fin E → N.Site)

/-- Public sparse ID of each cable in the dense physical presentation. -/
noncomputable def densePublicRows : (denseLayout N rows).Edge ↪ Fin E :=
  (denseSlot N rows).symm.toEmbedding.trans rows

/-- Going through the dense layout preserves the original sparse query number. -/
theorem densePublicRows_slot (e : N.Edge) : densePublicRows N rows (denseSlot N rows e) = rows e :=
  congrArg rows ((denseSlot N rows).symm_apply_apply e)

/-- The occupied sparse public rows are exactly the same set after the dense relabeling. -/
theorem densePublicRows_range : Set.range (densePublicRows N rows) = Set.range rows := by
  ext i
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨(denseSlot N rows).symm v,rfl⟩
  · rintro ⟨v,rfl⟩
    exact ⟨denseSlot N rows v,densePublicRows_slot N rows v⟩

/-- The same physical input bits represent the dense layout with sparse queries, including
the inactive loops reserved at the same sites. This is the presentation used with
`Packing.Names.localRecords_denseLayout`. -/
theorem represents_denseLayout {x : Inputs B S E k w → Bool} (h : Represents N site rows dummy x) :
    Represents (denseLayout N rows) site (densePublicRows N rows) dummy x := by
  apply represents_of_rows
  · intro v
    obtain ⟨e,rfl⟩ := (denseSlot N rows).surjective v
    rw [densePublicRows_slot]
    have src : (denseLayout N rows).src (denseSlot N rows e) = N.src e := src_slot N _ _ e
    have dst : (denseLayout N rows).dst (denseSlot N rows e) = N.dst e := dst_slot N _ _ e
    have width : (denseLayout N rows).width (denseSlot N rows e) = N.width e := width_slot N _ _ e
    rw [src,dst,width]
    constructor
    · intro side
      cases side
      · exact (h.addresses (rows e) false).trans (congrArg (fun s => (site s).val) (dst_slot N rows dummy e))
      · exact (h.addresses (rows e) true).trans (congrArg (fun s => (site s).val) (src_slot N rows dummy e))
    · exact (h.widths (rows e)).trans (width_slot N rows dummy e)
  · intro i hi
    rw [densePublicRows_range] at hi
    have hole := unused_row N rows dummy i hi
    constructor
    · intro side
      cases side
      · exact (h.addresses i false).trans (congrArg (fun s => (site s).val) hole.2.1)
      · exact (h.addresses i true).trans (congrArg (fun s => (site s).val) hole.1)
    · exact (h.widths i).trans hole.2.2

end Shortening.PublicEndpoints

end BorderVNP
end Computability
end OAI
