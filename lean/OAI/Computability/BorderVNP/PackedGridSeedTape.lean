import OAI.Computability.BorderVNP.PackedGridSidecar
import OAI.Computability.BorderVNP.PackedGridPaddingBudget
import OAI.Computability.BorderVNP.PackedSeedBoxRate
import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges

/-! # Exact fixed-length literal tapes for the actual prewired seed-grid boxes -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 2000000

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited InheritedBank Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped BigOperators Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance seedTapeDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _
local notation "V₀" => GridHosts.tileCount q depth
local notation "width₀" => fun _ : Fin V₀ => GridHosts.inputBlockWidth r n q depth
local notation "lane₀" => GridHosts.wiredLane G V₀ Fintype.card_pos
local notation "pack₀" => routedPacking position W.route (fun _ => le_rfl)
local notation "S₀" => seedSiteCapacity n r q depth
local notation "H₀" => seedChannelWidth n r q depth
local notation "K₀" => seedBoxCapacity n r q depth (Fintype.card (Direction q))
local notation "body₀" => bodyBudget K₀

/-- Each true grouped external lane belongs to the same cell as the physically
routed original attached leaf. -/
theorem seedLane_aligned (p : Fin r × Fin (publicWidth G)) :
    order (lane₀ p).1 = cell position W.route ((W.routedFine position).attach p) := by
  exact ((wiredFine G d D W.trees).slotPlace_attach finProdFinEquiv (wiredLayout G d W.trees).distinct_input_leaves order (r*n) _ p).symm

/-- The true public one-copy grid seen by the sparse-bank initializer, with one
common-width external word at each tile. -/
noncomputable abbrev seedGrouped :=
  grouped (H := H₀) (src := fun e : (Fin q → Deck (depth+2)) × Direction q => e.1)
    (dst := fun e => e.1 * step q (depth+2) e.2) (W.routedFine position) (cell position W.route) position width₀ order

/-- A public group contributes exactly one input word, and the wire bits come
from at most two cable endpoints per Cayley direction. -/
theorem seedIncoming_le (c : Fin q → Deck (depth+2)) :
    incoming (W.seedGrouped position) c ≤ 2*Fintype.card (Direction q)*H₀ + GridHosts.inputBlockWidth r n q depth := by
  rw [incoming_eq_widths]
  have hi : incidentWidth (W.seedGrouped position) c ≤ 2*Fintype.card (Direction q)*H₀ := by
    change (∑ _ : {e : (Fin q → Deck (depth+2)) × Direction q // e.1 = c ∨ e.1*step q (depth+2) e.2 = c}, H₀) ≤ _
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact Nat.mul_le_mul_right _ (GridPadding.cayley_ends (step q (depth+2)) c)
  have hp : portWidth (W.seedGrouped position) c = GridHosts.inputBlockWidth r n q depth := by
    change (∑ _ : {i : Fin V₀ // order i = c}, GridHosts.inputBlockWidth r n q depth) = _
    have ht : Fintype.card {i : Fin V₀ // order i = c} = 1 :=
      Fintype.card_eq_one_iff.mpr ⟨⟨order.symm c,order.apply_symm_apply _⟩,fun j => Subtype.ext (order.injective (j.property.trans (order.apply_symm_apply c).symm))⟩
    simp [ht]
  rw [hp]
  exact Nat.add_le_add_right hi _

variable (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))

/-- The complete private factor tape, including the staged source rows, actual
public-boundary ties, every zero constraint, and report suffix padding. -/
noncomputable abbrev seedStored : List Factor :=
  BottomGridBank.stored (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀ (W.seedLane_aligned position)
    siteID edgeID portID channelID groupID c (fun v => W.routedRules position (sidecarReport code) v.val) (3*S₀) S₀

/-- The initial physical site record repeats the same complete stored box in
each copy and ties its live external words to the one grouped tile input. -/
noncomputable abbrev seedBorn (copies : ℕ) : Inherited.Site :=
  BottomGridBank.born (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c
    (fun v => W.routedRules position (sidecarReport code) v.val) copies (3*S₀) S₀

/-- The actual compact report suffix, immediately after the true fine and public
incoming banks of one copy. -/
noncomputable abbrev seedPositions :=
  W.sidecarPositions position code siteID edgeID portID c (3*S₀+incoming (W.seedGrouped position) c)

private theorem seedDegree (v : (W.routedFine position).Site) : Fintype.card (CellBox.Lane (W.routedFine position) v) ≤ 3 :=
  let tri := (wiredFine G d D W.trees).trivalent_subdivide
    (BooleanLayout.trivalent (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d)) (wireRoutes position W.route)
  ((W.routedFine position).lane_count_le tri.1 v).trans (tri.2 v)

/-- Cardinality of the true immutable report positions fits the published common cap. -/
theorem seedPositions_length :
    (W.seedPositions position code siteID edgeID portID c).length ≤ S₀ := by
  rw [seedPositions,sidecarPositions,positions_length]
  apply (count_le_length _).trans
  simpa only [factors,List.length_map,siteList_length] using W.seed_sites_le position c

/-- Number of true fine-site records and full staged one-copy bank fit the published uniform capacity. -/
theorem seedBorn_room :
    Fintype.card {v : (W.routedFine position).Site // cell position W.route v = c} +
      bottomStride (3*S₀+incoming (W.seedGrouped position) c) S₀ ≤ K₀ := by
  have hs : Fintype.card {v : (W.routedFine position).Site // cell position W.route v = c} ≤ S₀ := W.seed_sites_le position c
  have hi := W.seedIncoming_le position c
  unfold bottomStride seedBoxCapacity
  omega

/-- Byte-for-byte encoded body of the actual box fits the reserved body region,
uniformly in the routes, field data and chosen physical row names. -/
theorem seedBody_room :
    (Packet.Source.boxBody (W.seedStored position code siteID edgeID portID channelID groupID c)).length ≤ body₀ := by
  apply stored_body_bits (W.routedFine position) (cell position W.route) position pack₀ width₀ order lane₀
    (W.seedLane_aligned position) siteID edgeID portID channelID groupID c
    (fun v => W.routedRules position (sidecarReport code) v.val) (3*S₀) S₀ (W.seed_stride_le position c)
    _ (W.seedDegree position) K₀ (W.seedBorn_room position c)
  simpa only [seedPositions,sidecarPositions,positions_length] using W.seedPositions_length position code siteID edgeID portID c

/-- A private literal of exactly the common published length, containing the
entire staged original box and its actual fixed-width report-position fields. -/
noncomputable def seedTape (header : ℕ) : Fin (seedDescriptionWidth n r q depth header body₀) → Bool :=
  Packet.Source.siteWithTally header body₀ (W.seedStored position code siteID edgeID portID channelID groupID c)
    (TallySidecar.bits header (W.seedPositions position code siteID edgeID portID c))

/-- Once the fixed literal is delivered, the opaque reader sees the full private
factor body and the tally reader sees the exact position words in its separate suffix. -/
theorem seedTape_delivered {w : ℕ} (mem : BurstRAM.Memory w) (header slot : ℕ)
    (received : ∀ j : Fin (seedDescriptionWidth n r q depth header body₀), (mem (slot+j.val)).val =
      (W.seedTape position code siteID edgeID portID channelID groupID c header j).toNat) :
    Packet.Source.Delivered (description := seedDescriptionWidth n r q depth header body₀)
        (fun a => (mem a).val) slot header (W.seedStored position code siteID edgeID portID channelID groupID c) ∧
      DiagonalTallyBits.WordsAt mem (slot+header+body₀) (TallySidecar.words header (W.seedPositions position code siteID edgeID portID c)) := by
  have hb := W.seedBody_room position code siteID edgeID portID channelID groupID c
  have hs := sidecar_room header body₀ _ (W.seedPositions_length position code siteID edgeID portID c)
  exact ⟨(Packet.Source.siteWithTally_read (fun a => (mem a).val) slot header body₀ _ _ hb hs received).1,
    TallySidecar.delivered_words mem slot header body₀ _ _ hb hs received⟩

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
