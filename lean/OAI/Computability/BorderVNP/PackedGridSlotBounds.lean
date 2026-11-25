import OAI.Computability.BorderVNP.PackedGridSlots
import OAI.Computability.BorderVNP.PackedGridLocalBounds

/-! # Counting the sites retained in the paper's padded initial slots

A live input occupies just one slot in its public block, and each internal site has a
different position in its internal block. A route adds one fine site per ordered visit.
The one-copy directory therefore has at most the two block capacities plus the public
congestion width many fine factors, independently of how the private routes were chosen.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Finset
open scoped Classical
variable {D n : ℕ} {P G : Type} {bits : P → ℕ} [Group G] [Fintype G]
variable (N : Network D P bits) (input : P ≃ Fin n) (inject : Function.Injective N.attach)
variable (order : Fin (Fintype.card G) ≃ G) (slots : ℕ) (fit : n ≤ slots)

/-- The public upper vertex budget and the slot budget bound the actual number of old
sites in every padded block. -/
theorem occupancy_slots {s : ℕ} (hv : Fintype.card N.Site ≤ s) (g : G) :
    (univ.filter fun v => N.slotPlace input inject order slots fit v = g).card ≤
      blockWidth slots (Fintype.card G) + blockWidth s (Fintype.card G) := by
  let addr := (N.slotIndex input inject slots fit).trans
    (initialAddress (Fintype.card_pos (α := G)) slots (Fintype.card N.OtherSite))
  let offset (v : {v : N.Site // N.slotPlace input inject order slots fit v = g}) := (addr v.val).2
  have hi : Function.Injective offset := by
    intro a b he
    exact Subtype.ext (addr.injective (Prod.ext (order.injective (a.property.trans b.property.symm)) he))
  have hcard := Fintype.card_le_of_injective offset hi
  have hOther := (Fintype.card_le_of_injective (fun v : N.OtherSite => v.val) Subtype.val_injective).trans hv
  apply le_trans _ (Nat.add_le_add_left ((gc_mul_ceilDiv (Fintype.card_pos (α := G))).monotone_l hOther) _)
  simp only [Fintype.card_subtype,Fintype.card_sum,Fintype.card_fin] at hcard
  convert! hcard using 2
  simp only [blockWidth,Network.OtherSite,Fintype.card_subtype]


variable {G J : Type} [Group G] [Fintype G] {step : J → G} {invStep : ∀ j, ∃ k, step k = (step j)⁻¹}
variable {place : N.Site → G} {k h : ℕ} (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (r : Routed N place step invStep k h)

/-- The number of fine factors stored in a routed cell is the number of original sites
there plus the exact number of added equality sites along all the ordered walks. -/
theorem routed_site_count (g : G) :
    Fintype.card {v : (N.subdivide (wireRoutes position r)).Site // cell position r v = g} =
      (univ.filter fun v => place v = g).card + ∑ e, (r.walk e).support.count g := by
  rw [Fintype.card_subtype]
  simp only [card_eq_sum_ones,sum_filter]
  erw [Fintype.sum_sum_type]
  congr 1
  erw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro e _
  exact WalkLayout.sum_vertex_hits _ (r.walk e) g

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
