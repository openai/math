import OAI.Computability.BorderVNP.PackedFrozenSignedPacketGeometry
import OAI.Computability.BorderVNP.PackedTerminalSignedHosts
import OAI.Computability.BorderVNP.DiagonalEnrichedSewnTagModels

/-! # The issued signed field representation on the enriched terminal network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Shortening.PreparedBins
open Packing.PhysicalEpochs
open Packing Packing.DeckGrid Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords
open Diagonal.ExternalSew TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open EnrichedOuter TeamScales VPVNP.VerifierNetwork
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
open CellPacketGeometry
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs
set_option quotPrecheck false
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
open Diagonal DiagonalResidueRAM Branch TeamContraction.ProcessorSlots RoutingISA.Pins GeometryAdvice GeometryFrameEncoding
attribute [local instance] portFintype
set_option maxHeartbeats 3000000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {R time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring R r time pins link inner n Edge)
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {σ : Type} [Fintype σ] {g : ℕ} {len : Fin n} {state : Fin g}
    (W : WiredWitness G len D (Fintype.card (Cube D)) d order state)
    (tag : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (table : (seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K) (x : σ → Bool)

local notation "axes" => Fintype.card (Cube D)
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r n
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "geom" => (plan.execute G order position σ).choose.eval x
local notation3 (prettyPrint := false) "a₀" => Boundary.seedState S G d order position copies table geom
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G order position copies
local notation3 (prettyPrint := false) "source" => plan.frozenStart G order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)

local notation3 (prettyPrint := false) "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch S (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G order position σ).choose


variable {rTime rPins ell rInner : ℕ} {Wire : Type}
    (actual : Wiring R r rTime rPins ell rInner n Wire) (count : (fan S)^T*copies=R+1)
    {cells k packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth S (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape S (d+1) T).sites ≤ 2^(60*logWidth r n)) (cf : cells ≤ 2^k)
    (hg : 0 < inputBlockWidth r n (Fintype.card (Cube D)) d) (short : inputBlockWidth r n (Fintype.card (Cube D)) d ≤ ell)
    (pw : copies*inputBlockWidth r n (Fintype.card (Cube D)) d < 2^(60*logWidth r n))
    (extend : 60*logWidth r n ≤ packetWidth) (room : 15*(S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor) < 2^(60*logWidth r n))
    (hook : Compiled.HookRoom S T (60*logWidth r n) (initialMass (D:=D) n r d copies headerFactor))
    (q : (packHistory (plan.frozenLeaf G order position W tag sites edges ports table x) plan.compiled.machine.epoch T).Index)

local notation3 (prettyPrint := false) "s₁" => ((packHistory seed₀ (compiled).machine.epoch T).term q).val
local notation3 (prettyPrint := false) "N₀" => (flattenPack T (s₁).pack).layout
local notation3 (prettyPrint := false) "code₁" => ((compiled).machine.nativeCode seed₀ base x rfl widths ord fit q).val
local notation3 (prettyPrint := false) "input₁" => Retained.branch aug (broadcastOrder (fan S) widths ord T) fit x code₁
local notation3 (prettyPrint := false) "prior₁" => (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ q
local notation "offs" => flatOffset (compiledOffset S (d+1)) T
local notation "g₁" => inputBlockWidth r n axes d
local notation3 (prettyPrint := false) "p₁" => (⟨R,r,actual.program.length+rTime,ell,g₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "hp₁" => (⟨hg,short,gridRoom actual Fintype.card_pos⟩ : (p₁).Valid)
local notation3 (prettyPrint := false) "h₁" => attachedHosts actual Fintype.card_pos count N₀
local notation3 (prettyPrint := false) "lane₁" => groupedLane actual tiles Fintype.card_pos ((fan S)^T) copies count
local notation3 (prettyPrint := false) "edge₁" => mergedEdges p₁ hp₁ (s₁).rows.edge
local notation3 (prettyPrint := false) "port₁" => (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "oldPort" => Flat.portRows T (privatePorts S key T)
local notation3 (prettyPrint := false) "finalN" => finalLayout p₁ h₁
local notation3 (prettyPrint := false) "cells₁" => fun v => cellNumber (reduceMove (EnrichedOuter.depth S (d+1) T) ((s₁).route.origin v))
local notation3 (prettyPrint := false) "F₀" => TerminalCells.fields (Move := allowedMoves (Cube D) S.budget) (q := axes)
  (d := EnrichedOuter.depth S (d+1) T) (E := (boundaryShape S (d+1) T).edges) vf cf (@groupRow ((fan S)^T) tiles offs)
  (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "route₁" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFormat
local notation3 (prettyPrint := false) "ext₁" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFormat true
local notation3 (prettyPrint := false) "source₁" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₁ ext₁)
local notation3 (prettyPrint := false) "F₁" => FieldExport.fields F₀ p₁ (attachedName offs copies)
local notation3 (prettyPrint := false) "source₂" => stagedSource F₁ source₁
local notation3 (prettyPrint := false) "F₂" => Fields.widenWidths (stagedFields F₁) extend (Sum.inr false)
local notation3 (prettyPrint := false) "hist₁" => stagedHistory (Sewn.terminalHistory epochFormat (F₀).sites
  (Grid.physicalOperands actual Fintype.card_pos count hg short F₀ (attachedName offs copies) FinalTies.routePresent))
local notation3 (prettyPrint := false) "saved₁" => (Retained.Terminal.saved epochFormat).eval input₁

/-- The issued field and its actual evaluated operand on this terminal history. -/
noncomputable abbrev frozenIssuedReportGeometry := (F₂,(source₂).eval input₁)

local notation3 (prettyPrint := false) "attachedProgram[" h "]" => sewnPrograms N₀ lane₁ (h).bundle
  (fun _ : FreeBlock R tiles => g₁) (freeLane hg (gridRoom actual Fintype.card_pos)) (h).groupOwner
    ((h).groupAligned hg (gridRoom actual Fintype.card_pos)) (s₁).rows.edge oldPort edge₁ port₁ prior₁

include pw room hook in
/-- The reached signed field names the actual enriched sites, cables, grouped
ports, and private widths. Equality of the two host assignments transports
the already evaluated field; all registers and inputs stay on the same q. -/
theorem frozen_issued_enriched_rep
    (installed : (seed₀).val.pack.layout = (wiredGrid actual axes d order position).groupedRepeat
      (fun _ : Fin tiles => g₁) order copies) :
    let N := enrichedSewnLayout actual axes d order position count (compiled).machine seed₀ installed q
    let ps := enrichedSewnPrograms actual axes d order position count (compiled).machine seed₀ installed oldPort hp₁ q prior₁
    Packing.CellAddressPhysical.Represents N cells₁ (fun v => (ps v).program.size) (s₁).rows.site edge₁ port₁ F₂ ((source₂).eval input₁) := by
  intro N ps
  let attach := h₁
  let retained := enrichedBlockHosts actual axes d order position count (compiled).machine seed₀ installed q
  have same : attach = retained :=
    enrichedBlockHosts_attached actual axes d order position count (compiled).machine seed₀ installed q
  have rep := (plan.frozen_signed_packet_geometry G order position W tag sites edges ports table x wr hm
    seeds number widths ord fit actual count cellNumber vf cf hg short pw extend room hook q).2.1
  change Packing.CellAddressPhysical.Represents (finalLayout p₁ attach) cells₁ (fun v => ((attachedProgram[attach]) v).program.size)
    (s₁).rows.site edge₁ port₁ F₂ ((source₂).eval input₁) at rep
  rw [same] at rep
  exact rep

/-- The emitted cell's private dimension is exactly the original enriched
network's dimension. Both the network and all site program sizes are
transported along the equality of the two host assignments for this history. -/
theorem frozen_enriched_externalBase
    (installed : (seed₀).val.pack.layout = (wiredGrid actual axes d order position).groupedRepeat
      (fun _ : Fin tiles => g₁) order copies) (c : Fin cells) :
    let N := enrichedSewnLayout actual axes d order position count (compiled).machine seed₀ installed q
    let ps := enrichedSewnPrograms actual axes d order position count (compiled).machine seed₀ installed oldPort hp₁ q prior₁
    Packing.CellAddresses.externalBase (finalLayout p₁ h₁) cells₁ c (fun v => ((attachedProgram[h₁]) v).program.size) =
      Packing.CellAddresses.externalBase N cells₁ c (fun v => (ps v).program.size) := by
  intro N ps
  let attach := h₁
  let retained := enrichedBlockHosts actual axes d order position count (compiled).machine seed₀ installed q
  have same : attach=retained :=
    enrichedBlockHosts_attached actual axes d order position count (compiled).machine seed₀ installed q
  change Packing.CellAddresses.externalBase (finalLayout p₁ attach) cells₁ c (fun v => ((attachedProgram[attach]) v).program.size) =
    Packing.CellAddresses.externalBase (finalLayout p₁ retained) cells₁ c (fun v => ((attachedProgram[retained]) v).program.size)
  rw [same]

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
