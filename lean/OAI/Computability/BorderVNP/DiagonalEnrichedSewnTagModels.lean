import OAI.Computability.BorderVNP.PackedHistorySewnTagModels
import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedSum
import OAI.Computability.BorderVNP.DiagonalEnrichedHistoryTags
import OAI.Computability.BorderVNP.FiniteCandidateSewnRows

/-! # The actual signed private programs at the exterior-sewn grid

The old edge names occupy the first directory segment. Each new partner
interval uses its four-slot ordinal, and each grouped literal or pin lane
uses the team-major free-port order. The complete signed tags at each
retained host are read from its birth program on the restored old input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch Inherited
open scoped BigOperators Classical BorderVNP.Epoch.Cube

set_option synthInstance.maxSize 2048
set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

universe u

variable {D m start T : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)

local notation "tiles" => GridHosts.tileCount axes gridDepth
local notation "block" => GridHosts.inputBlockWidth r n axes gridDepth
local notation "params" => fieldSewParams G axes gridDepth
local notation "state" q => Subtype.val (ProfileSum.term (packHistory bottom (Machine.epoch M) T) q)
local notation "network" q => Pack.layout (flattenPack T (EnrichedOuter.State.pack (state q)))
local notation "hosts" q => enrichedBlockHosts G axes gridDepth order position count M bottom installed q
local notation "sewn" q => enrichedSewnLayout G axes gridDepth order position count M bottom installed q

variable {np : ℕ} (oldPort : (Fin ((fan S)^T) × Fin (GridHosts.tileCount axes gridDepth)) ↪ Fin np)
variable (hp : (fieldSewParams G axes gridDepth).Valid) (q : (packHistory bottom M.epoch T).Index)
variable (progs : Site.Programs (flattenPack T ((packHistory bottom M.epoch T).term q).val.pack).layout)

/-- The retained program on each actual sewn host. Its last stage uses the
native old-edge, new-wire and grouped free-port directories. -/
noncomputable def enrichedSewnPrograms : Site.Programs (sewn q) :=
  let h := hosts q
  let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
  let lane := GridHosts.groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
  SewnField.sewnPrograms (network q) lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge oldPort
    (FieldExport.mergedEdges params hp (state q).rows.edge) finProdFinEquiv.toEmbedding progs

variable {Team Param Gadget Hidden : Type} [Fintype Team] [Fintype Param] {exp : ℕ}
    (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, MvPolynomial.eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      MvPolynomial.eval₂Hom (Int.castRingHom E) y f = 0)
    (pos : e.Entry → Gadget) (base : Hidden → Tracked Team Param Gadget exp bottom.val.pack.layout)

/-- Enumerate the nested original team owners of the tagged terminal. -/
noncomputable local instance teamFinite {j : ℕ} : Fintype (Port (fan S) Team j) := Replay.batchFinite (fan S) Team j

/-- For every local assignment of a sewn site, including assignments on cut
cables, the tagged entry has its true ordered observation fiber and scalar
counts at that site's unchanged birth predicate. -/
theorem enrichedSewnTagModels (z : Fin ((fan S)^T) → Hidden) (number : Gadget ↪ ℕ)
    (pred : (network q).Site → (ℕ → Bool) → Prop)
    (model : Site.Programs.TagModels (network q) (state q).rows.edge oldPort progs
      (EnrichedOuterReplay.terminal M y hy pos bottom base q z).flat.tags number pred) :
    Site.Programs.TagModels (sewn q) (FieldExport.mergedEdges params hp (state q).rows.edge)
      finProdFinEquiv.toEmbedding
      (enrichedSewnPrograms G axes gridDepth order position count M bottom installed oldPort hp q progs)
      (enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hp.block q z).tags
      number pred := by
  let h := hosts q
  let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
  let lane := GridHosts.groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
  exact SewnField.sewnTagModels (network q) lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge oldPort
    (FieldExport.mergedEdges params hp (state q).rows.edge) finProdFinEquiv.toEmbedding progs _ number pred model

/-- Each unary power position keeps its owner. At every independent local
assignment the old and sewn host read the same full entry and the same
selected powers, on the incidence vector reconstructed in native row order. -/
theorem enrichedSewn_hostReads (z : Fin ((fan S)^T) → Hidden) :
    let old := (EnrichedOuterReplay.terminal M y hy pos bottom base q z).flat
    let final := enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hp.block q z
    let h := hosts q
    let room := GridHosts.gridRoom G (show 0 < tiles from Fintype.card_pos)
    let lane := GridHosts.groupedLane G tiles Fintype.card_pos ((fan S)^T) copies count
    let edge := FieldExport.mergedEdges params hp (state q).rows.edge
    let read := SewnField.sewnRead (network q) lane h.bundle (fun _ : FreeBlock R tiles => block)
      (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge oldPort
      edge finProdFinEquiv.toEmbedding
    final.words.site = old.words.site ∧ ∀ v wire port, ∃ oldWire oldInput,
      (∀ k, (read v k).elim false (inputWords (sewn q) edge finProdFinEquiv.toEmbedding v wire port) =
        inputWords (network q) (state q).rows.edge oldPort v oldWire oldInput k) ∧
      final.tags v wire port = old.tags v oldWire oldInput ∧
      final.words.selected v wire port = old.words.selected v oldWire oldInput := by
  intro old final h room lane edge read
  refine ⟨rfl,fun v wire port => ?_⟩
  obtain ⟨inputs,tags⟩ := SewnField.sewnRead_table (network q) lane h.bundle (fun _ : FreeBlock R tiles => block)
    (freeLane hp.block room) h.groupOwner (h.groupAligned hp.block room) (state q).rows.edge oldPort
    edge finProdFinEquiv.toEmbedding old.tags v wire port
  exact ⟨_,_,inputs,tags,rfl⟩

attribute [-instance] teamFinite
attribute [local instance] BorderVNP.Epoch.Round.portFintype

/-- From the birth programs on the original grid, the entire attained
history and the exterior sewing preserve their independently chosen work
at the real physical host of each leaf. -/
theorem terminalSewnTagModels (rows : ∀ j hj, (M j hj).F.SiteRows) {capacity : ℕ → ℕ}
    (ports : ∀ j, Port (fan S) (Fin tiles) j ↪ Fin (capacity j))
    (layout : ∀ j hj, (M j hj).FieldRows (rows j hj) (ports j) (ports (j+1)))
    (number : Gadget ↪ ℕ) (seedPrograms : Site.Programs bottom.val.pack.layout)
    (condition : Hidden → bottom.val.pack.layout.Site → (ℕ → Bool) → Prop)
    (seed : ∀ h, Site.Programs.TagModels bottom.val.pack.layout bottom.val.rows.edge (ports 0)
      seedPrograms (base h).tags number (condition h)) (z : Fin ((fan S)^T) → Hidden) :
    Site.Programs.TagModels (sewn q) (FieldExport.mergedEdges params hp (state q).rows.edge)
      finProdFinEquiv.toEmbedding
      (enrichedSewnPrograms G axes gridDepth order position count M bottom installed (Flat.portRows T (ports T)) hp q
        (M.terminalPrivatePrograms rows (number ∘ pos) bottom seedPrograms q))
      (@Tracked.tags _ _ _ (Port (fan S) Team T) Param Gadget (Replay.batchFinite (fan S) Team T) inferInstance exp _
        (enrichedSewnTerm G axes gridDepth order position count M bottom installed y hy pos base hp.block q z))
      number (Site.Programs.carryPred (enrichedOuterHosts M bottom q).site (fun v => condition (z v.1) v.2)) := by
  apply enrichedSewnTagModels
  exact M.terminalPrivatePrograms_tagModels rows ports layout y hy pos number bottom seedPrograms base condition seed q z

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
