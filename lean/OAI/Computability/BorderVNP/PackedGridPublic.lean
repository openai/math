import OAI.Computability.BorderVNP.PackedGridInitial

/-! # A public width and topology independent of the batch network

The public input ordinal fixes each external leaf's tile. A vertex budget suffices
to select a common capacity for all neighbor cables and all batch realizations
of this size, including networks with different private vertex counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridPlacement

open Crossing Finset
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} {G J : Type} [Group G] [Fintype G] [Fintype J]
variable (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) (step : J → G)
variable {n : ℕ} (input : P ≃ Fin n) (order : Fin (Fintype.card G) ≃ G)

/-- Public endpoint-multiplicity budget depending only on the number of slots, the
host size and a common upper bound on the number of fine vertices. -/
def endpointBudget (n s V : ℕ) := 3 * (blockWidth n V + blockWidth s V)

/-- The public grid and external port directory are reconstructed without a fine
network, a choice of private routes, or any of its table entries. -/
def publicGrid (bits : P → ℕ) (s h : ℕ) : Network D P bits where
  Site := G
  Edge := G × J
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src q := q.1
  dst q := q.1 * step q.2
  width _ := cableWidth G (endpointBudget n s (Fintype.card G)) h
  attach p := order (leafSlot (Fintype.card_pos (α := G)) n (input p)).1
  position g := (position g).val
  in_ball g := (position g).property

variable (N : Network D P bits) (inject : Function.Injective N.attach)

/-- The upper bound on the number of fine sites covers the actual number of internal
sites, including when some public blocks are empty. -/
theorem initialLoad_le {s : ℕ} (hv : Fintype.card N.Site ≤ s) :
    N.initialLoad input G ≤ endpointBudget n s (Fintype.card G) := by
  have ht := (Fintype.card_le_of_injective (fun x : N.OtherSite => x.val) Subtype.val_injective).trans hv
  have hh := (gc_mul_ceilDiv (Fintype.card_pos (α := G))).monotone_l ht
  exact Nat.mul_le_mul_left 3 (Nat.add_le_add_left hh _)

omit [Fintype J] in
/-- The private routing certifies the prescribed public cap even when its fine network
uses fewer sites than allowed by the public vertex budget. -/
theorem routed_public (invStep : ∀ j, ∃ k, step k = (step j)⁻¹) {s h : ℕ}
    (hv : Fintype.card N.Site ≤ s)
    (degree : ∀ v, (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card ≤ 3)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) :
    Nonempty (Routed N (N.initialPlace input inject order) step invStep
      (endpointBudget n s (Fintype.card G)) h) := by
  obtain ⟨r⟩ := N.routed_initial step invStep input inject order degree short
  refine ⟨r.walk,fun g => (r.visits g).trans ?_⟩
  have hh := initialLoad_le (G := G) input N hv
  unfold cableWidth
  gcongr

/-- Exposing just the canonical neighbor and leaf names gives exactly this public
layout. Only the private site tables depend on the actual fine circuit. -/
theorem grid_eq_public (s h : ℕ) :
    N.cayleyGrid (N.initialPlace input inject order) position step
      (cableWidth G (endpointBudget n s (Fintype.card G)) h) =
        publicGrid position step input order bits s h := by
  unfold Network.cayleyGrid Network.uniformGrid publicGrid
  congr 1
  funext p
  exact N.initialPlace_attach input inject order p

include inject in
/-- Any bounded-volume degree-three bit network is realized on the common public grid.
One local table per cell works simultaneously for every external input. -/
theorem public_tables {R : Type*} [CommSemiring R] (invStep : ∀ j, ∃ k, step k = (step j)⁻¹)
    {s h : ℕ} (hv : Fintype.card N.Site ≤ s) (unit : ∀ e, N.width e ≤ 1)
    (degree : ∀ v, (univ.filter fun e => N.src e = v).card + (univ.filter fun e => N.dst e = v).card ≤ 3)
    (short : ∀ u : G, ∃ w : List J, w.length ≤ h ∧ (w.map step).prod = u) (table : N.Tables R) :
    ∃ t : (publicGrid position step input order bits s h).Tables R, ∀ x,
      (publicGrid position step input order bits s h).value t x = N.value table x := by
  obtain ⟨r⟩ := routed_public step input order N inject invStep hv degree short
  rw [← grid_eq_public position step input order N inject]
  exact exists_tables position r unit table

end Packing.GridPlacement

end BorderVNP
end Computability
end OAI
