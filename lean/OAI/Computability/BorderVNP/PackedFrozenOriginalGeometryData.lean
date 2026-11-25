import OAI.Computability.BorderVNP.PackedFrozenOriginalIssuedDirectory
import OAI.Computability.BorderVNP.CellPacketGeometryOriginalInputs

/-! # All original directory operands on one frozen history -/

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
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native CellPacketGeometry.LiveWords
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs CellSparse.Packet SiteWords
set_option quotPrecheck false
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {teams time pins link inner : ℕ} {Edge : Type} [Fintype Edge] (G : Wiring teams r time pins link inner n Edge)
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
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms S order position W tag sites edges ports table geom
local notation3 "fmt" => Boundary.seedFormat G order position copies
local notation3 "source" => plan.frozenStart G order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G order position W tag sites edges ports table x

variable (wr : WidthRanges S (d+1) T (60*logWidth r n)) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S (d+1) t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (number : e.Entry → ℕ)

local notation3 "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess S (d+1) (fun _ _ => 60*logWidth r n) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan S) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch S (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan S) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G order position σ).choose


variable {R rTime rPins ell rInner : ℕ} {Wire : Type}
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
local notation3 (prettyPrint := false) "rawState" => sewnPrograms N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
    (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
    (s₁).rows.edge oldPort edge₁ port₁ prior₁
local notation3 (prettyPrint := false) "scp" => (epochFormat).schema.append
  (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*tiles) w)

open private oldWire from OAI.Computability.BorderVNP.PackedTerminalStagedFields
variable (dir : Directory.Layout) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (cellPos : 0 < cells)
local notation "H₁" => boundaryShape S (d+1) T
local notation "J₁" => (fan S)^T*tiles
local notation "live₁" => (R+1)*tiles
local notation "actualShape" => (⟨(H₁).sites,(H₁).edges+(p₁).slots⟩ : Shape)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := J₁}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J₁ → Fin (H₁).sites)
local notation3 (prettyPrint := false) "occupied₁" => fun i => oldWire (FinalTies.sewnPresent p₁ FinalTies.routePresent i)
variable {tagCap : ℕ} (arena stride gap desc gadgets digits : ℕ)
local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((H₁).edges+(p₁).slots) live₁ packetWidth
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "signed₁" => SignedFields.liveFrame F₂ boxes₁ old₁ arena stride gap desc gadgets digits
local notation3 (prettyPrint := false) "feeds₁" => Terminal.feeds (s:=actualShape) F₂ occupied₁ (fun _ => true) boxes₁ hist₁ signed₁ (.inr true)
variable (hs : ∀ j, (((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
local notation3 (prettyPrint := false) "read₁" => Sum.elim ((source₂).eval input₁) saved₁
local notation3 (prettyPrint := false) "cell₁" => TerminalTable.cell F₂ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "bit₁" => TerminalTable.bitStart F₂ ((source₂).eval input₁)
local notation3 (prettyPrint := false) "box₁" => TerminalTable.boxStart F₂ boxes₁ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "args₁" => (feeds₁).arguments read₁
local notation3 (prettyPrint := false) "directory₁" => directory scp final₁ boxes₁ hs hf priv₁ reports₁
  args₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁

local notation3 (prettyPrint := false) "original" => originalDescriptionRows (compiled).machine seed₀ q publicDir rfl order

local notation3 (prettyPrint := false) "entry₁" => (original).trans (s₁).rows.site
local notation3 (prettyPrint := false) "known₁" => historyRoster S (d+1) number (fun _ => []) T

/-- The historical and final schemas, their original embedded anchor rows,
and the previously returned address and geometry fields of this history. -/
noncomputable def issuedOriginalGeometry : CellPacketGeometry.History.OriginalGeometry J₁ cells where
  nr := (H₁).sites
  cap := tagCap
  oldWidth := _
  tieWidth := _
  OldAT := _
  OldBT := _
  TieAT := _
  TieBT := _
  Scope := _
  oldSchema := scp
  tieSchema := final₁
  inputEntry := entry₁
  known := known₁
  oldCap := hs
  tieCap := hf
  privateArgs := priv₁
  reportArgs := reports₁
  geometryArg := args₁
  oldPins := (hist₁).eval read₁
  tiePins := (feeds₁).binding.eval read₁
  originCell := cell₁
  oldOff := bit₁
  oldBox := box₁

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
