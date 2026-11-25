import OAI.Computability.BorderVNP.PackedSeedSewnCaps
import OAI.Computability.BorderVNP.PackedSeedBirthMass
import OAI.Computability.BorderVNP.PackedSeedCellRecords
import OAI.Computability.BorderVNP.PackedGridSeedTape
import OAI.Computability.BorderVNP.PackedSiteRecords

/-!
# Initial public and expanded site caps of the actual wired verifier

The original site has one public box name and a fixed number of grouped ties.
Its private descriptor, single stored factor sweep, replicated work slab and
replicated visits are all charged to the expanded account on the same tile.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open Cover GridPlacement TeamScales Diagonal.ExternalSew

/-- Uniform bound on one plus the original public local record count. -/
def seedPublicBase (degree : ℕ) := 1036*(2*degree+2)+2*degree+4

/-- Uniform bound on one plus the original expanded local record count,
including the full private delivery charged once per repeated copy. -/
def baseMass (degree cap H copies dB : ℕ) :=
  seedPublicBase degree + 12 + 810487*cap + copies*(2*cap+dB+(2*degree+1)*H)

/-- The fixed geometric direction catalog determines one coefficient for both
initial caps, independently of the amount of private verifier data. -/
theorem baseMass_scale (n r q depth degree copies dB : ℕ) (hc : 0 < copies) :
    let A := seedPublicBase degree + 12 + 810489*(11+2*degree) + (2*degree+1) + 1
    let H := seedChannelWidth n r q depth
    seedPublicBase degree ≤ A*copies ∧
    baseMass degree (seedBoxCapacity n r q depth degree) H copies dB ≤ A*copies*(1+H+dB) := by
  intro A H
  have hk : seedBoxCapacity n r q depth degree ≤ (11+2*degree)*H := seedBoxCapacity_le ..
  let B := seedPublicBase degree+12
  have hB : B ≤ B*copies := Nat.le_mul_of_pos_right _ hc
  have hK : 810487*seedBoxCapacity n r q depth degree ≤ copies*(810487*((11+2*degree)*H)) :=
    (Nat.mul_le_mul_left 810487 hk).trans (Nat.le_mul_of_pos_left _ hc)
  have hw := Nat.mul_le_mul_left copies (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) dB) ((2*degree+1)*H))
  have hA : seedPublicBase degree ≤ A := by dsimp only [A]; omega
  refine ⟨hA.trans (Nat.le_mul_of_pos_right _ hc),?_⟩
  change B+810487*seedBoxCapacity n r q depth degree+copies*(2*seedBoxCapacity n r q depth degree+dB+(2*degree+1)*H) ≤ _
  apply (Nat.add_le_add (Nat.add_le_add hB hK) hw).trans
  let D := 810489*(11+2*degree)+(2*degree+1)
  have hBD : B ≤ A := by dsimp only [A,B]; omega
  have hDA : D ≤ A := by dsimp only [D,A]; omega
  have h1 : 1 ≤ A := by dsimp only [A]; omega
  calc
    _ = copies*(B+D*H+1*dB) := by dsimp only [D]; ring
    _ ≤ copies*(A+A*H+A*dB) := Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add hBD
      (Nat.mul_le_mul_right _ hDA)) (Nat.mul_le_mul_right _ h1))
    _ = A*copies*(1+H+dB) := by ring

end Packing.DeckGrid

namespace Packing.DeckGrid.WiredWitness

open Cover Crossing Diagonal.CellEntries TeamContraction GridPlacement Shortening Shortening.Adaptive
open Diagonal.ExternalSew GridBoxes BottomReports BottomGridBank Inherited Epoch Epoch.Round PhysicalEpochs
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
open private seedDegree from OAI.Computability.BorderVNP.PackedGridSeedTape

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (GridHosts.tileCount q depth) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Use the same decision for product-deck equality in the routed grid and its incidence tests. -/
noncomputable local instance seedBaseDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "V₀" => GridHosts.tileCount q depth
local notation "width₀" => fun _ : Fin V₀ => GridHosts.inputBlockWidth r n q depth
local notation "lane₀" => GridHosts.wiredLane G V₀ Fintype.card_pos
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "S₀" => seedSiteCapacity n r q depth
local notation "H₀" => seedChannelWidth n r q depth
local notation "deg" => Fintype.card (Direction q)
local notation "K₀" => seedBoxCapacity n r q depth deg

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {ns ne np qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin ns)
    (edgeID : (W.routedFine position).Edge ↪ Fin ne) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin np)
    (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa)

local notation "site" => W.seedBorn position code siteID edgeID portID channelID groupID

set_option maxHeartbeats 1800000 in
/-- The genuine private birth program pays the fixed public row count and
the complete one-copy static and repeated dynamic cost on its original tile. -/
theorem seedBirth_metrics (c : Fin q → Deck (depth+2)) (copies : ℕ) :
    (site c copies).publicNodes ≤ 1036*(2*deg+2) ∧
    (site c copies).staticNodes ≤ 1036*(2*deg+2)+12+810487*K₀ ∧
    (site c copies).expandedLoad ≤ copies*(2*K₀) := by
  let fine := W.routedFine position
  let b := W.seedStored position code siteID edgeID portID channelID groupID c
  let stride := bottomStride (3*S₀+incoming (W.seedGrouped position) c) S₀
  let N := W.seedGrouped position
  let factors := fun v : {v : fine.Site // cell position W.route v=c} => W.routedRules position (sidecarReport code) v.val
  have hroom := W.seedBorn_room position c
  have hcount : Fintype.card (BottomRepeat.Row N c) ≤ 2*deg+1 := by
    have hinc : Fintype.card (Incident N c) ≤ 2*deg := GridPadding.cayley_ends (step q (depth+2)) c
    let eqv : Attached N c ≃ Unit := Equiv.ofBijective (fun _ => ()) ⟨by
      intro x y _
      apply Subtype.ext
      exact order.injective (x.property.trans y.property.symm),fun _ => ⟨⟨order.symm c,order.apply_symm_apply _⟩,rfl⟩⟩
    have hport : Fintype.card (Attached N c) = 1 := (Fintype.card_congr eqv).trans Fintype.card_unique
    change Fintype.card (Incident N c ⊕ Attached N c) ≤ _
    rw [Fintype.card_sum,hport]
    exact Nat.add_le_add_right hinc 1
  have hlen : b.length ≤ K₀ := (stored_length_le fine (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c factors (3*S₀) S₀
    (W.seed_stride_le position c)).trans hroom
  have hh := born_charges fine (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c factors (3*S₀) S₀ copies
    (W.seed_stride_le position c) (seedDegree W position)
  have hm := hh.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hroom) 1)
  have hs := hh.2.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hroom) 5)
  have bound := BottomRepeat.bornWith_static_charge N channelID groupID c copies (3*S₀) stride b K₀ hm hs
  have pub := BottomRepeat.bornWith_publicNodes N channelID groupID c copies (3*S₀) stride b
  have row : 1+Fintype.card (BottomRepeat.Row N c) ≤ 2*deg+2 := by omega
  refine ⟨pub.trans (Nat.mul_le_mul_left _ row),bound.trans (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ row) _) _),?_⟩
  exact BottomRepeat.bornWith_expandedLoad N channelID groupID c copies (3*S₀) stride b K₀
    ((Nat.le_add_left _ _).trans hroom) hlen

variable (copies dB : ℕ)
local notation "N₀" => seedBundle G q depth order position copies

/-- The two physical accounting modes share the true birth program. The
sparse account omits delivered private tables, while the expanded one
charges every factor, sweep, work lane, visit and padded private bit. -/
noncomputable def seedFields (expanded : Bool) : RecordData N₀ :=
  ⟨fun v => if expanded then (site v copies).staticNodes else (site v copies).publicNodes,
    fun v => (site v copies).expandedLoad + copies*dB⟩

local notation "fields" => W.seedFields position code siteID edgeID portID channelID groupID copies dB

/-- Both local bounds at the original physical tile of each verifier birth
program. All unused channel positions have their true declared widths. -/
theorem seedFields_cell (c : Fin q → Deck (depth+2)) :
    1+localRecords N₀ false (fields false).prior (fields false).payload (fun v => v=c) ≤ seedPublicBase deg ∧
    1+localRecords N₀ true (fields true).prior (fields true).payload (fun v => v=c) ≤ baseMass deg K₀ H₀ copies dB := by
  have hm := W.seedBirth_metrics position code siteID edgeID portID channelID groupID c copies
  rw [seed_localRecords G q depth order position copies false,seed_localRecords G q depth order position copies true]
  simp only [seedFields,boxCost,recordCost,Bool.false_eq_true,ite_false,ite_true,add_zero]
  refine ⟨?_,?_⟩
  · dsimp only [seedPublicBase]
    omega
  · have hg := Nat.mul_le_mul_left copies (seed_capacity_le n r q depth).1
    have bound := Nat.add_le_add hm.2.1 hm.2.2
    dsimp only [baseMass,seedPublicBase]
    nlinarith only [bound,hg]

/-- The original route bank, using any integral lifts of the same numbered
tiles, satisfies the exact sparse and expanded geometric input caps. -/
theorem seedFields_siteCap {K : Type*} (table : (N₀).Tables K) {I : Type} [Fintype I] {L : ℝ}
    (route : SiteRoutes (Pack.mk N₀ table) I (depth+1) L)
    (coord : (Fin q → Deck (depth+2)) ≃ (I → Deck (depth+2)))
    (origins : ∀ v, reduceMove (depth+1) (route.origin v) = coord v) :
    SiteCap route (fields false) false (seedPublicBase deg) ∧
      SiteCap route (fields true) true (baseMass deg K₀ H₀ copies dB) := by
  have test (c : I → Deck (depth+2)) : (fun v => reduceMove (depth+1) (route.origin v) = c) =
      (fun v => v=coord.symm c) := by
    funext v; rw [origins]; exact propext coord.eq_symm_apply.symm
  constructor
  · intro c; rw [test c]
    exact (W.seedFields_cell position code siteID edgeID portID channelID groupID copies dB _).1
  · intro c; rw [test c]
    exact (W.seedFields_cell position code siteID edgeID portID channelID groupID copies dB _).2

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
