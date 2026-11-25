import OAI.Computability.BorderVNP.PackedCongestion
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fin.Embedding

/-! # Public grid of initial boxes in Proposition 7.2

Leaves occupy successive blocks in processor/field/position order. Internal vertices cycle
through the sites. This placement bounds the number of port incidences before a private
intermediate site is chosen for each wire.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Finset
open scoped Classical

/-- The integral public block length for storing `count` items over `sites` cells. -/
def blockWidth (count sites : ℕ) : ℕ := count ⌈/⌉ sites

private theorem le_total_width {sites : ℕ} (hs : 0 < sites) (count : ℕ) :
    count ≤ sites * blockWidth count sites := (ceilDiv_le_iff_le_mul hs).mp le_rfl

/-- The row-major address of a leaf. In the linear input order, the site changes only after a
whole block of width `⌈leaves / sites⌉` has been consumed. -/
def leafSlot {sites : ℕ} (hs : 0 < sites) (leaves : ℕ) :
    Fin leaves ↪ Fin sites × Fin (blockWidth leaves sites) :=
  (Fin.castLEEmb (le_total_width hs leaves)).trans finProdFinEquiv.symm.toEmbedding

/-- Internal vertices cycle through the sites before taking a second slot in any site. -/
def internalSlot {sites : ℕ} (hs : 0 < sites) (other : ℕ) :
    Fin other ↪ Fin sites × Fin (blockWidth other sites) :=
  ((Fin.castLEEmb ((le_total_width hs other).trans_eq (Nat.mul_comm ..))).trans
    finProdFinEquiv.symm.toEmbedding).trans (Equiv.prodComm _ _).toEmbedding

/-- The full address distinguishes a leaf from an internal vertex even if their local slot
numbers coincide. -/
def initialAddress {sites : ℕ} (hs : 0 < sites) (leaves other : ℕ) :
    (Fin leaves ⊕ Fin other) ↪ Fin sites × (Fin (blockWidth leaves sites) ⊕ Fin (blockWidth other sites)) where
  toFun
    | .inl i => ((leafSlot hs leaves i).1, .inl (leafSlot hs leaves i).2)
    | .inr j => ((internalSlot hs other j).1, .inr (internalSlot hs other j).2)
  inj' := by
    rintro (i | i) (j | j) h <;> simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, and_false] at h
    · exact congrArg Sum.inl ((leafSlot hs leaves).injective (Prod.ext h.1 h.2))
    · exact congrArg Sum.inr ((internalSlot hs other).injective (Prod.ext h.1 h.2))

/-- The number of vertices at any initial site, with both public block widths rounded up. -/
theorem initial_occupancy {sites : ℕ} (hs : 0 < sites) (leaves other : ℕ) (s : Fin sites) :
    (univ.filter fun v => (initialAddress hs leaves other v).1 = s).card ≤
      blockWidth leaves sites + blockWidth other sites := by
  let e := initialAddress hs leaves other
  let slot (v : {v // (e v).1 = s}) := (e v.val).2
  have hinj : Function.Injective slot := by
    intro i j h
    exact Subtype.ext (e.injective (Prod.ext (i.property.trans j.property.symm) h))
  simpa [Fintype.card_subtype] using Fintype.card_le_of_injective slot hinj

private theorem placed_endpoints_le {G V W : Type*} [DecidableEq G] [DecidableEq V] [Fintype V] [Fintype W]
    (place : V → G) (endpt : W → V) {occupancy degree : ℕ} (g : G)
    (ho : (univ.filter fun v => place v = g).card ≤ occupancy)
    (hd : ∀ v, (univ.filter fun e => endpt e = v).card ≤ degree) :
    (univ.filter fun e => place (endpt e) = g).card ≤ degree * occupancy := by
  classical
  let atSite := univ.filter fun v => place v = g
  calc
    _ = ∑ v ∈ atSite, (univ.filter fun e => endpt e = v).card := by
      simpa [atSite] using (sum_card_fiberwise_eq_card_filter univ atSite endpt).symm
    _ ≤ ∑ _ ∈ atSite, degree := sum_le_sum (fun v _ => hd v)
    _ ≤ _ := by simpa [mul_comm] using Nat.mul_le_mul_left degree ho

/-- The private routes for a degree-three bit network can all be chosen after the public leaf
and internal-vertex layout has been fixed. The bound depends only on the numbers of vertices,
sites and path length, independently of the contents of the local tables. -/
theorem exists_initial_routing {G W : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype W]
    (order : Fin (Fintype.card G) ≃ G) {leaves other h : ℕ} (path : G → Finset G)
    (left right : W → Fin leaves ⊕ Fin other)
    (degree : ∀ v, (univ.filter fun w => left w = v).card +
      (univ.filter fun w => right w = v).card ≤ 3)
    (hpath : ∀ g, (path g).card ≤ h) :
    let place := fun v => order ((initialAddress (Fintype.card_pos (α := G)) leaves other v).1)
    let m := blockWidth leaves (Fintype.card G) + blockWidth other (Fintype.card G)
    ∃ middle : W → G, ∀ s : G,
      (∑ w : W, (routeVisit path (place ∘ left) (place ∘ right) w s (middle w) : ℝ)) ≤
        8 * (3 * m : ℕ) * h + Real.log (Fintype.card G) := by
  classical
  let a := initialAddress (Fintype.card_pos (α := G)) leaves other
  let place := fun v => order (a v).1
  let m := blockWidth leaves (Fintype.card G) + blockWidth other (Fintype.card G)
  have ho (g : G) : (univ.filter fun v => place v = g).card ≤ m := by
    simp only [place, ← Equiv.eq_symm_apply]
    exact initial_occupancy (Fintype.card_pos (α := G)) leaves other _
  have hl (g : G) := placed_endpoints_le (degree := 3) place left g (ho g)
    (fun v => by have := degree v; omega)
  have hr (g : G) := placed_endpoints_le (degree := 3) place right g (ho g)
    (fun v => by have := degree v; omega)
  exact exists_low_congestion_routes path (place ∘ left) (place ∘ right) (3 * m) h hl hr hpath

end Packing

end BorderVNP
end Computability
end OAI
