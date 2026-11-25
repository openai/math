import OAI.Computability.BorderVNP.DiagonalExternalSewEnrichedLayout
import OAI.Computability.BorderVNP.PackedSeedSelectedCaps
import OAI.Computability.BorderVNP.PackedSeedInstalledCaps

/-!
# Exterior sewing with the true verifier birth metadata

The complete enriched history carries the initialized public or expanded
fields of the wired witness. Its physical exterior records are charged at
their actual final grid tiles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Adaptive Packing Packing.DeckGrid
open PackedHistoryCircuit PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.EnrichedOuter
open PublicCapacity CellEntries TeamContraction ParseBatch
open BorderVNP.Epoch.Round Packing.PhysicalEpochs
open scoped BigOperators Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u

variable {D m start T : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} {shape : ℕ → Shape} {W : ℕ → Type} [∀ t, Fintype (W t)]
    {V : ℕ → ℕ → Type} [∀ t j, Fintype (V t j)] {w : ℕ → ℕ → ℕ}
    {R r t pins link inner n copies : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ) (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {deep : S.floor+1+S.drop*T ≤ start} (count : (fan S)^T*copies = R+1)
    {good : ∀ j, EnrichedOuter.State S start (Fin (GridHosts.tileCount axes gridDepth))
      (fun _ => copies*GridHosts.inputBlockWidth r n axes gridDepth) shape W j → Prop}
    (M : EnrichedOuter.Machine.{0,u} deep good V w) (bottom : Admissible good 0)
    (installed : bottom.val.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth)
      order copies)


variable {grammarStates : ℕ} {parseRoot : Fin n} {parseState : Fin grammarStates}
    (witness : WiredWitness G parseRoot D axes gridDepth order parseState)
    (code : VPVNP.GrammarLabel (Fin n × Bool) (Fin grammarStates) n ↪ ℕ)
    {ns ne np qe qa : ℕ} (siteID : (witness.routedFine position).Site ↪ Fin ns)
    (edgeID : (witness.routedFine position).Edge ↪ Fin ne)
    (portID : (Fin r × Fin (Prewire.publicWidth G)) ↪ Fin np)
    (channelID : ((Fin axes → Deck (gridDepth+2)) × Direction axes) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount axes gridDepth) ↪ Fin qa)
    (dB : ℕ)
    (coord : (Fin axes → Deck (gridDepth+2)) ≃ (Epoch.Cube D → Deck (depth S start 0+1)))
    (origins : ∀ v, reduceMove (depth S start 0) (bottom.val.route.origin v) =
      coord (cast (congrArg Network.Site installed) v))

local notation "seedData" => witness.installedSeedFields position code siteID edgeID portID channelID groupID copies dB installed
local notation "degree₀" => Fintype.card (Direction axes)
local notation "expanded₀" => baseMass degree₀ (seedBoxCapacity n r axes gridDepth degree₀)
  (seedChannelWidth n r axes gridDepth) copies dB

include origins in
set_option maxHeartbeats 1600000 in
/-- Exact bounds for every reachable enriched output histogram after adding
all physical exterior wires. Both modes track fields of the same real
birth boxes and of the same chosen sequence of shortening terms. -/
theorem enrichedSewn_seedBounds (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (small : GridHosts.inputBlockWidth r n axes gridDepth ≤ link) (i : (packHistory bottom M.epoch T).Index)
    (tile : Epoch.Cube D → Deck (depth S start T+1)) :
    let state := ((packHistory bottom M.epoch T).term i).val
    let records := fun ex => M.historyFields bottom (seedData ex) T i
    let load :=  fun ex => localRecords (enrichedSewnLayout G axes gridDepth order position count M bottom installed i)
      ex (records ex).prior (records ex).payload (fun v => reduceMove (depth S start T) (state.route.origin v) = tile)
    load false ≤ 5*copies*(S.recordFactor^T*seedPublicBase degree₀) ∧
      load true ≤ 7*(S.recordFactor^T*expanded₀) := by
  intro state records cost
  obtain ⟨hpub,hex⟩ := witness.installedSeed_cap position code siteID edgeID portID channelID groupID copies dB
    installed bottom.val.route coord origins
  let original := Fin (GridHosts.tileCount axes gridDepth)
  let localCap (ex : Bool) (B : ℕ) (f : Fintype original) :=
    @SiteCap D K original (Epoch.Cube D) f _ _ _ _ bottom.val.pack bottom.val.route (seedData ex) ex B
  have transfer (ex : Bool) (B : ℕ) (h : localCap ex B (Fin.fintype _)) :
      localCap ex B (portFintype (P := original) (k := fan S) (b := 0)) :=
    (congrArg (localCap ex B) (Subsingleton.elim _ _)).mpr h
  exact ⟨enrichedSewn_historyRecords G axes gridDepth order position count M bottom installed (seedData false) false
    (seedPublicBase degree₀) (transfer _ _ hpub) hg small i tile,
    enrichedSewn_historyRecords G axes gridDepth order position count M bottom installed (seedData true) true
      expanded₀ (transfer _ _ hex) hg small i tile⟩

include origins in
/-- The integral per-cell thresholds of Proposition 7.2 on this very same
sewn pack. The two numerical premises are supplied simultaneously by
`DeckGrid.eventually_seed_actual_caps` at the schedule's selected depth. -/
theorem enrichedSewn_seedThresholds (hg : 0 < GridHosts.inputBlockWidth r n axes gridDepth)
    (small : GridHosts.inputBlockWidth r n axes gridDepth ≤ link)
    (sparse : 5*copies*(S.recordFactor^T*seedPublicBase degree₀) ≤ TeamScales.width n (1/100))
    (expanded : 7*(S.recordFactor^T*expanded₀) ≤ TeamScales.width n (1/5))
    (i : (packHistory bottom M.epoch T).Index) (tile : Epoch.Cube D → Deck (depth S start T+1)) :
    let state := ((packHistory bottom M.epoch T).term i).val
    let records := fun ex => M.historyFields bottom (seedData ex) T i
    let load :=  fun ex => localRecords (enrichedSewnLayout G axes gridDepth order position count M bottom installed i)
      ex (records ex).prior (records ex).payload (fun v => reduceMove (depth S start T) (state.route.origin v) = tile)
    load false ≤ TeamScales.width n (1/100) ∧ load true ≤ TeamScales.width n (1/5) := by
  intro state records cost
  obtain ⟨hp,hm⟩ := enrichedSewn_seedBounds G axes gridDepth order position count M bottom installed witness
    code siteID edgeID portID channelID groupID dB coord origins hg small i tile
  exact ⟨hp.trans sparse,hm.trans expanded⟩

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
