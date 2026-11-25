import OAI.Computability.BorderVNP.PackedGridPublic

/-! # The paper's padded block width for the live external slots

The prewired tensor exposes only literal, exterior-link and pin positions. Nevertheless
the block width is computed from the full processor-slot budget `r*n`. Embedding the
live ordinals as an initial segment leaves the unused positions empty. In particular
it introduces neither new graph vertices nor artificial external ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open BorderVNP.Packing
open scoped Classical
variable {D n : ℕ} {P G : Type} {bits : P → ℕ} [Group G] [Fintype G]
variable (N : Network D P bits) (input : P ≃ Fin n) (inject : Function.Injective N.attach)
variable (order : Fin (Fintype.card G) ≃ G) (slots : ℕ) (fit : n ≤ slots)

/-- Live leaves occupy the first `n` positions of the public slot space. The remaining
vertices retain their private internal numbering. -/
noncomputable def slotIndex : N.Site ↪ Fin slots ⊕ Fin (Fintype.card N.OtherSite) :=
  (N.siteOrder input inject).toEmbedding.trans
    ((Fin.castLEEmb fit).sumMap (Function.Embedding.refl _))

/-- Actual cell of each fine site using the paper's prescribed number of slots. -/
noncomputable def slotPlace (v : N.Site) : G :=
  order ((initialAddress (Fintype.card_pos (α := G)) slots (Fintype.card N.OtherSite)
    (N.slotIndex input inject slots fit v)).1)

/-- For every live port, the public slot address uses the full block width
`ceil(slots / card G)` and the original live ordinal. -/
theorem slotPlace_attach (p : P) :
    N.slotPlace input inject order slots fit (N.attach p) =
      order (leafSlot (Fintype.card_pos (α := G)) slots ((input p).castLE fit)).1 := by
  unfold slotPlace slotIndex
  simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,siteOrder_attach]
  rfl

end Crossing.Network

namespace Packing.GridPlacement

open Crossing Finset
open scoped Classical
variable {D n : ℕ} {P G J : Type} {bits : P → ℕ} [Group G] [Fintype G]
variable (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (step : J → G)
variable (input : P ≃ Fin n) (order : Fin (Fintype.card G) ≃ G)

/-- Public host with the exact paper block width, including empty positions at its end. -/
def publicGridSlots [Fintype J] (bits : P → ℕ) (slots : ℕ) (fit : n ≤ slots) (s h : ℕ) :
    Network D P bits where
  Site := G
  Edge := G × J
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src q := q.1
  dst q := q.1 * step q.2
  width _ := cableWidth G (endpointBudget slots s (Fintype.card G)) h
  attach p := order (leafSlot (Fintype.card_pos (α := G)) slots ((input p).castLE fit)).1
  position g := (position g).val
  in_ball g := (position g).property

variable (N : Network D P bits) (inject : Function.Injective N.attach) (slots : ℕ) (fit : n ≤ slots)

/-- A sparse initial segment of live leaves has exactly the same route guarantee as
the full initial slot layout. The vertex budget also bounds all nonleaf blocks. -/
theorem routed_public_slots (invStep : ∀ j, ∃ k, step k = (step j)⁻¹) {s h : ℕ}
    (hv : Fintype.card N.Site ≤ s)
    (degree : ∀ v, (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card ≤ 3)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    Nonempty (Routed N (N.slotPlace input inject order slots fit) step invStep
      (endpointBudget slots s (Fintype.card G)) h) := by
  obtain ⟨p,hp⟩ := CayleyPaths.simple_paths step invStep h short
  let idx := N.slotIndex input inject slots fit
  have hd (v) : (univ.filter fun e => idx (N.src e) = v).card +
      (univ.filter fun e => idx (N.dst e) = v).card ≤ 3 := by
    by_cases used : v ∈ Set.range idx
    · obtain ⟨w,rfl⟩ := used
      simpa only [idx.injective.eq_iff] using degree w
    · have missing (w : N.Site) : idx w ≠ v := fun eq => used ⟨w,eq⟩
      simp [missing]
  have hs (u : G) : (CayleyPaths.sites step invStep p u).card ≤ h+1 := by
    rw [CayleyPaths.sites,List.toFinset_card_of_nodup (p u).nodup_support,(p u).val.length_support]
    exact Nat.succ_le_succ (hp u)
  obtain ⟨mid,hm⟩ := exists_initial_routing order (CayleyPaths.sites step invStep p)
    (fun e => idx (N.src e)) (fun e => idx (N.dst e)) hd hs
  let cell := N.slotPlace input inject order slots fit
  let left := cell ∘ N.src
  let right := cell ∘ N.dst
  refine ⟨fun e => CayleyPaths.route step invStep p (left e) (right e) (mid e),fun g => ?_⟩
  have hOther := (Fintype.card_le_of_injective (fun v : N.OtherSite => v.val) Subtype.val_injective).trans hv
  have hcap : 3*(blockWidth slots (Fintype.card G) + blockWidth (Fintype.card N.OtherSite) (Fintype.card G)) ≤
      endpointBudget slots s (Fintype.card G) := Nat.mul_le_mul_left _ (Nat.add_le_add_left
        ((gc_mul_ceilDiv (Fintype.card_pos (α := G))).monotone_l hOther) _)
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_sum]
  apply (Finset.sum_le_sum fun e _ => Nat.cast_le.mpr (CayleyPaths.count_route step invStep p left right e (mid e) g)).trans
  apply (hm g).trans
  apply le_trans _ (real_bound_le_cableWidth G (endpointBudget slots s (Fintype.card G)) h)
  simp only [Nat.cast_add,Nat.cast_one]
  gcongr

/-- The final geometry, port directory and neighbor widths have precisely their
publicly prescribed values after all the choices of private paths. -/
theorem grid_eq_public_slots [Fintype J] (s h : ℕ) :
    N.cayleyGrid (N.slotPlace input inject order slots fit) position step
      (cableWidth G (endpointBudget slots s (Fintype.card G)) h) =
        publicGridSlots position step input order bits slots fit s h := by
  unfold Network.cayleyGrid Network.uniformGrid publicGridSlots
  congr 1
  funext p
  exact N.slotPlace_attach input inject order slots fit p

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
