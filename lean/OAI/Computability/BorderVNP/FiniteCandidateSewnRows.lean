import OAI.Computability.BorderVNP.FiniteDiagonalSewnGrid
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldRows
import OAI.Computability.BorderVNP.FiniteSewnFieldLanes
import OAI.Computability.BorderVNP.FiniteCandidatePortNames
import OAI.Computability.BorderVNP.DiagonalPayloadBound

/-! # Actual sparse row names and exterior lane reads of a finite candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch FiniteDiagonal
open Inherited
open scoped BigOperators Classical BorderVNP.Epoch.Cube

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
universe u

variable {D m start T : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (volume : ℕ)
    (installed : bottom.val.pack.layout = (FinitePrewire.fieldGrid G axes gridDepth order position volume).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)


/-- The rectangle of four potential exterior intervals per original team and tile. -/
noncomputable abbrev fieldSewParams : FieldExport.Params :=
  ⟨R,r,G.program.length+t,link,GridHosts.inputBlockWidth r n axes gridDepth,GridHosts.tileCount axes gridDepth⟩

local notation "params" => fieldSewParams G axes gridDepth
local notation "groups" => (fan S)^T
local notation "tiles" => GridHosts.tileCount axes gridDepth
local notation "block" => GridHosts.inputBlockWidth r n axes gridDepth
local notation "state" q => Subtype.val (ProfileSum.term (packHistory bottom (Machine.epoch M) T) q)
local notation "network" q => Pack.layout (flattenPack T (EnrichedOuter.State.pack (state q)))
local notation "sewn" q => fieldSewnLayout G axes gridDepth order position count M bottom volume installed q
local notation "hosts" q => fieldBlockHosts G axes gridDepth order position count M bottom volume installed q

/-- The physical retained sites keep their names, the old cables keep their
stored IDs, and the new cables occupy exactly their live four-slot ordinals. -/
noncomputable def fieldSewnRows (hp : (params).Valid) (q : (packHistory bottom M.epoch T).Index) :
    Rows ⟨(shape T).sites,(shape T).edges+(params).slots⟩ (sewn q) :=
  ⟨(state q).rows.site,FieldExport.mergedEdges params hp (state q).rows.edge⟩

/-- Read an old local incidence lane by its exact source ordinal after
sewing. A vacant old grid lane has no source and reads zero. -/
noncomputable def fieldSewnRead (hp : (params).Valid) (q : (packHistory bottom M.epoch T).Index) (v : (network q).Site) :
    Fin (incoming (network q) v) → Option (Fin (incoming (sewn q) v)) :=
  let h := hosts q
  let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
  let lane := GridHosts.groupedLane G tiles Fintype.card_pos groups copies count
  SewnField.sewnRead (network q) lane h.bundle (fun _ : FreeBlock R tiles => block) (freeLane hp.block room)
    h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge (SelectedSchedule.fieldIncomingPorts S tiles T)
    (fieldSewnRows G axes gridDepth order position count M bottom volume installed hp q).edge finProdFinEquiv.toEmbedding v

/-- The restored old local word and the actual sewn scalar table use the
same sources at each site. All slots are interpreted in their true physical
directories, including loops, unoccupied old lanes and padded intervals. -/
theorem fieldSewnRead_table (hp : (params).Valid) (q : (packHistory bottom M.epoch T).Index) (v : (network q).Site)
    (z : ∀ a : Incident (sewn q) v, Fin ((sewn q).width a.val) → Bool)
    (x : ∀ _ : Attached (sewn q) v, Fin block → Bool) :
    let rows := fieldSewnRows G axes gridDepth order position count M bottom volume installed hp q
    let read := fieldSewnRead G axes gridDepth order position count M bottom volume installed hp q v
    ∃ (oldZ : ∀ a : Incident (network q) v, Fin ((network q).width a.val) → Bool)
      (oldX : ∀ _ : Attached (network q) v, Fin (copies*block) → Bool),
      (∀ k, (read k).elim false (inputWords (sewn q) rows.edge finProdFinEquiv.toEmbedding v z x) =
        inputWords (network q) (state q).rows.edge (SelectedSchedule.fieldIncomingPorts S tiles T) v oldZ oldX k) ∧
      sewnFieldTable G axes gridDepth order position count M bottom volume installed hp.block q v z x =
        (flattenPack T (state q).pack).table v oldZ oldX := by
  let h := hosts q
  let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
  let lane := GridHosts.groupedLane G tiles Fintype.card_pos groups copies count
  let rows := fieldSewnRows G axes gridDepth order position count M bottom volume installed hp q
  have same := SewnField.sewnRead_table (network q) lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge
    (SelectedSchedule.fieldIncomingPorts S tiles T) rows.edge finProdFinEquiv.toEmbedding (flattenPack T (state q).pack).table v z x
  exact ⟨_,_,same⟩

/-- Reinterpreting the finite candidate's real input lanes and partner
intervals preserves each scalar occurrence bound at its original vertex. -/
theorem fieldSewn_payloadBound {Owner Param Gadget : Type} [Fintype Owner] [Fintype Param] {exp : ℕ}
    (q : (packHistory bottom M.epoch T).Index) (hg : 0 < block)
    (tag : Tracked Owner Param Gadget exp (network q)) (payload : (network q).Site → ℕ)
    (old : PayloadBound tag.tags payload) :
    let lane := GridHosts.groupedLane G tiles Fintype.card_pos groups copies count
    PayloadBound ((hosts q).grouped hg (GridHosts.gridRoom G Fintype.card_pos)
      (FineView.tracked (network q) lane tag)).tags payload :=
  fun v _ _ g => old v _ _ g

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
