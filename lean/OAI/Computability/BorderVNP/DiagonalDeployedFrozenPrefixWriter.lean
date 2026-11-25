import OAI.Computability.BorderVNP.DiagonalFrozenReturnInputs
import OAI.Computability.BorderVNP.DiagonalSignedBareHeaderReceipts
import OAI.Computability.BorderVNP.DiagonalSignedSelectedCandidates
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection
import OAI.Computability.BorderVNP.DiagonalFrozenPublishedPin
import OAI.Computability.BorderVNP.DiagonalFrozenRawCandidate
import OAI.Computability.BorderVNP.DiagonalDeployedSupportedHistories
import OAI.Computability.BorderVNP.DiagonalDeployedJointFront
import OAI.Computability.BorderVNP.DiagonalSignedLocatedWriterRoom
import OAI.Computability.BorderVNP.DiagonalFrozenPublicationOperands
import OAI.Computability.BorderVNP.DiagonalFrozenPublicationTransport
import OAI.Computability.BorderVNP.DiagonalFrozenHeaderTransport
import OAI.Computability.BorderVNP.PackedFrozenTapedInstallation
import OAI.Computability.BorderVNP.PackedFrozenChosenPublication

/-! # Publishing the selected frozen history on the deployed joint prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule EnrichedOuter
open Shortening Shortening.Adaptive Packing.Inherited
open BorderVNP.Epoch BorderVNP.Epoch.Round
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins RoutingISA.Evaluator RoutingISA.CompactMachine
open scoped Classical BigOperators BorderVNP.Epoch.Cube
attribute [local instance] portFintype

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} [NeZero D] {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {characteristic lenPred s : ℕ} {literalOrder : Fin (lenPred+1) × Bool ≃ Fin (2*(lenPred+1))}
    {C : CommonField paid aux characteristic lenPred s literalOrder} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r rw pinWidth pc a link ec d : ℕ}
    (reader : ChosenReader chart (R+1) r rw rw rw pinWidth) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc 64 32 8) (basis : SiteData R r 64 32 rw a)
    (machineFit : fitsWith physical 64 32 r rw a R link (lenPred+1) ec)
local notation "indexWidth" => (pairedTableParameters (lenPred+1) s+2)*pinWidth
local notation "tail" => setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)

local notation "axes" => Fintype.card (Epoch.Cube D)
variable {order : Fin (GridHosts.tileCount (Fintype.card (Epoch.Cube D)) d) ≃ (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
        (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a))
        physical machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) (Fin.last lenPred) D (Fintype.card (Epoch.Cube D)) d order
        (0 : ParseTable.State (Fin (lenPred+1) × Bool) s))
    (position : (Fin (Fintype.card (Epoch.Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
      (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)) physical machineFit
      ((pairedTableParameters (lenPred+1) s+2)*pinWidth))) ↪ Fin np)
    {T copies headerFactor Q : ℕ} {schedule : PackedHistoryCircuit.Normalized.SiteSchedule paid}
    (plan : PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan schedule (lenPred+1) r d T copies headerFactor Q)
    (wireLayout : Routing.WireLayout (R+1) r link)
    {σ : Type} [Fintype σ] (x : σ → Bool)
local notation3 (prettyPrint := false) "G₀" => tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw)
  (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
variable (seedTable : (seedBundle (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec)
      (width:=rw+1) (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)) physical
      machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) (Fintype.card (Epoch.Cube D)) d order position copies).Tables K)
open PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan
open TerminalCells FieldExport GridHosts Diagonal.ExternalSew.RowTrace Packing.CellAddressCircuit Packing.SewnField
open scoped Classical BorderVNP.Epoch.Cube
open CellPacketGeometry CellPacketGeometry.History CellPacketGeometry.History.Native CellPacketGeometry.LiveWords
open Packing.CellAddresses Packing.CellAddressPhysical Packing.RoutingOutputs CellSparse.Packet SiteWords
set_option quotPrecheck false
open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ParseBatchSort
open Diagonal DiagonalResidueRAM Branch TeamContraction.ProcessorSlots RoutingISA.Pins GeometryAdvice GeometryFrameEncoding
attribute [local instance] portFintype
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

open Packing.PhysicalEpochs Shortening.PublicCapacity Shortening.PreparedBins Packing.Inherited.FrozenTape Packing.Inherited.WorkWords RoutingISA.CompactMachine

local notation3 (prettyPrint := false) "signedTag" => ParseTable.signedLiteralCode (s:=s) literalOrder
local notation "tiles" => GridHosts.tileCount axes d
local notation "w" => 60*logWidth r (lenPred+1)
local notation "V" => CoverScale.sites (Cube D) (d+1)
local notation "extent" => copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
local notation "header" => WorkWords.grouped V extent
local notation "key" => Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
local notation3 (prettyPrint := false) "geom" => (plan.execute G₀ order position σ).choose.eval x
local notation3 (prettyPrint := false) "old₀" => Boundary.seedBirthPrograms schedule order position W signedTag sites edges ports seedTable geom
local notation3 (prettyPrint := false) "fmt" => Boundary.seedFormat G₀ order position copies
local notation3 (prettyPrint := false) "source" => plan.frozenStart G₀ order position σ

local notation3 (prettyPrint := false) "seed₀" => plan.frozenLeaf G₀ order position W signedTag sites edges ports seedTable x

variable (wr : WidthRanges schedule (d+1) T (60*logWidth r (lenPred+1))) (hm : 0 < m)
    (seeds : ∀ t, ∀ i : Fin schedule.rounds,
      ((Cube D → Deck (schedule.level (offset schedule (d+1) t) (i.val+1)+1)) × (schedule.source.pattern i).bins.Bin) → ℕ)
    (number : paid.Entry → ℕ)

local notation3 (prettyPrint := false) "compiled" => plan.compiled
local notation3 (prettyPrint := false) "steps" => (compiled).tapeSteps fmt header key wr hm
local notation3 (prettyPrint := false) "names" => (compiled).privateSiteRows key seeds


variable {reserve : ℕ} (widths : ℕ → ℕ)
    (ord : ∀ j, Machine.Guess schedule (d+1) (fun _ _ => 60*logWidth r (lenPred+1)) j ≃ Fin (widths j))
    (fit : broadcastWidth (fan schedule) widths T ≤ reserve)

local notation3 (prettyPrint := false) "epochFormat" => ProgramSchemas.epoch schedule (d+1) w fmt T
local notation3 (prettyPrint := false) "aug" => compile steps T le_rfl (repeatLeaf (fan schedule) source T)
local notation3 (prettyPrint := false) "base" => (plan.execute G₀ order position σ).choose


local notation3 (prettyPrint := false) "actual" => wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
local notation3 (prettyPrint := false) "rTime" => cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
  (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
variable (count : (fan schedule)^T*copies=R+1)
    {cells ownerBits packetWidth : ℕ} (cellNumber : (Cube D → Deck (EnrichedOuter.depth schedule (d+1) T+1)) ≃ Fin cells)
    (vf : (boundaryShape schedule (d+1) T).sites ≤ 2^(60*logWidth r (lenPred+1))) (cf : cells ≤ 2^ownerBits)
    (hg : 0 < inputBlockWidth r (lenPred+1) (Fintype.card (Cube D)) d) (short : inputBlockWidth r (lenPred+1) (Fintype.card (Cube D)) d ≤ link)
    (pw : copies*inputBlockWidth r (lenPred+1) (Fintype.card (Cube D)) d < 2^(60*logWidth r (lenPred+1)))
    (extend : 60*logWidth r (lenPred+1) ≤ packetWidth) (room : 15*(schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor) < 2^(60*logWidth r (lenPred+1)))
    (hook : Compiled.HookRoom schedule T (60*logWidth r (lenPred+1)) (initialMass (D:=D) (lenPred+1) r d copies headerFactor))
    (histQ : (packHistory (plan.frozenLeaf (tapeTemplate physical machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) order position W (ParseTable.signedLiteralCode literalOrder) sites edges ports seedTable x) plan.compiled.machine.epoch T).Index)

local notation3 (prettyPrint := false) "s₁" => ((packHistory seed₀ (compiled).machine.epoch T).term histQ).val
local notation3 (prettyPrint := false) "N₀" => (flattenPack T (s₁).pack).layout
local notation3 (prettyPrint := false) "code₁" => ((compiled).machine.nativeCode seed₀ base x rfl widths ord fit histQ).val
local notation3 (prettyPrint := false) "input₁" => Retained.branch aug (broadcastOrder (fan schedule) widths ord T) fit x code₁
local notation3 (prettyPrint := false) "prior₁" => (compiled).machine.terminalPrivatePrograms names number seed₀ old₀ histQ
local notation "offs" => flatOffset (compiledOffset schedule (d+1)) T
local notation "g₁" => inputBlockWidth r (lenPred+1) axes d
local notation3 (prettyPrint := false) "p₁" => (⟨R,r,(actual).program.length+rTime,link,g₁,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "hp₁" => (⟨hg,short,gridRoom actual Fintype.card_pos⟩ : (p₁).Valid)
local notation3 (prettyPrint := false) "h₁" => attachedHosts actual Fintype.card_pos count N₀
local notation3 (prettyPrint := false) "lane₁" => groupedLane actual tiles Fintype.card_pos ((fan schedule)^T) copies count
local notation3 (prettyPrint := false) "edge₁" => mergedEdges p₁ hp₁ (s₁).rows.edge
local notation3 (prettyPrint := false) "port₁" => (finProdFinEquiv : FreeBlock R tiles ≃ Fin ((R+1)*tiles)).toEmbedding
local notation3 (prettyPrint := false) "oldPort" => Flat.portRows T (privatePorts schedule key T)
local notation3 (prettyPrint := false) "finalN" => finalLayout p₁ h₁
local notation3 (prettyPrint := false) "cells₁" => fun v => cellNumber (reduceMove (EnrichedOuter.depth schedule (d+1) T) ((s₁).route.origin v))
local notation3 (prettyPrint := false) "F₀" => TerminalCells.fields (Move := allowedMoves (Cube D) schedule.budget) (q := axes)
  (d := EnrichedOuter.depth schedule (d+1) T) (E := (boundaryShape schedule (d+1) T).edges) vf cf (@groupRow ((fan schedule)^T) tiles offs)
  (fun _ => copies*g₁)
local notation3 (prettyPrint := false) "route₁" => Retained.Terminal.route (X := σ) (reserve := reserve) epochFormat
local notation3 (prettyPrint := false) "ext₁" => Retained.Terminal.width (X := σ) (reserve := reserve) epochFormat true
local notation3 (prettyPrint := false) "source₁" => withSewnFields (boundFrame (factorEnum D) cellNumber cf route₁ ext₁)
local notation3 (prettyPrint := false) "F₁" => FieldExport.fields F₀ p₁ (attachedName offs copies)
local notation3 (prettyPrint := false) "source₂" => stagedSource F₁ source₁
local notation3 (prettyPrint := false) "F₂" => Fields.widenWidths (stagedFields F₁) extend (Sum.inr false)
local notation3 (prettyPrint := false) "rawState" => sewnPrograms N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
    (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
    (s₁).rows.edge oldPort edge₁ port₁ prior₁
local notation3 (prettyPrint := false) "scp" => (epochFormat).schema.append
  (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*tiles) w)

open private oldWire staged_old from OAI.Computability.BorderVNP.PackedTerminalStagedFields
open private profilePaths_eq from OAI.Computability.BorderVNP.PackedHistoryChosenReservedGeometry

local notation3 (prettyPrint := false) "desc" => seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
  (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
variable (hardwareTemplate : SignedTaskArena.Layout) (sitePos : 0 < (boundaryShape schedule (d+1) T).sites)
    (cellPos : 0 < cells) (ownerFits : ownerBits ≤ packetWidth)
local notation "H₁" => boundaryShape schedule (d+1) T
local notation "J₁" => (fan schedule)^T*tiles
local notation "live₁" => (R+1)*tiles
local notation3 (prettyPrint := false) "dir₁" => freeDirectory R r ((actual).program.length+rTime) link tiles g₁ J₁ desc
local notation3 (prettyPrint := false) "publicDir" => {(dir₁) with sites := tiles, entries := J₁}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos

local notation3 (prettyPrint := false) "task₁" => hardwareTemplate.withNetwork cells ((H₁).edges+(p₁).slots)
variable {qbits tagCap : ℕ} (gadgets digits : ℕ)
    (ctrlFit : ∀ i : Fin 37, (hardwareTemplate.withNetwork cells ((boundaryShape schedule (d+1) T).edges+
      4*(R+1)*(GridHosts.tileCount (Fintype.card (Cube D)) d))).controls i.val < 2^packetWidth)
local notation3 (prettyPrint := false) "ctrl₁" => fun i : Fin 37 => (⟨(task₁).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
local notation3 (prettyPrint := false) "dataArena" => (task₁).cube.cellBank
local notation3 (prettyPrint := false) "dataStride" => (task₁).cube.cellStride
local notation3 (prettyPrint := false) "dataGap" => (task₁).p.privateGap
local notation3 (prettyPrint := false) "hosts₁" => originalDescriptionRows plan.compiled.machine seed₀ histQ dir₁ rfl order
local notation3 (prettyPrint := false) "livePorts" => Function.Embedding.refl (Fin (R+1) × Fin tiles)

local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((H₁).edges+(p₁).slots) live₁ packetWidth
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
variable (hs : ∀ j, (((ProgramSchemas.epoch schedule (d+1) (60*logWidth r (lenPred+1)) (Boundary.seedFormat (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw) (e:=ec)
      (width:=rw+1) (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)) physical
      machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r (lenPred+1)))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape schedule (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
    (keyFits : 60*logWidth r (lenPred+1)≤qbits) (sitesFit : (boundaryShape schedule (d+1) T).sites<2^qbits)
    (keysFit : cells+1<2^ownerBits) (sw : ∀ j, ((ProgramSchemas.epoch schedule (d+1) (60*logWidth r (lenPred+1)) (Boundary.seedFormat (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw) (e:=ec)
      (width:=rw+1) (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)) physical
      machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r (lenPred+1)))).width j≤packetWidth)
local notation3 (prettyPrint := false) "tpl₁" => template scp final₁ boxes₁ hs hf priv₁ reports₁
variable (pad : (roster (boundaryShape schedule (d+1) T).sites ((ProgramSchemas.epoch schedule (d+1) (60*logWidth r (lenPred+1)) (Boundary.seedFormat (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw) (e:=ec)
      (width:=rw+1) (k:=lenPred) (a:=setupWidth (rw+1) (lenPred+1)+(prefixCapacity r 32 64 rw (lenPred+1)+1+a)) physical
      machineFit ((pairedTableParameters (lenPred+1) s+2)*pinWidth)) order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r (lenPred+1)))) (FinalTies.tieSchema ((boundaryShape schedule (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth)).length<2^qbits)
    (dest hdr : ℕ)

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ) (shapes : Fin ((fan schedule)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "packetSize" => signedGridOutputCount ((H₁).edges+4*(R+1)*tiles) cells J₁ live₁
  37 (Total (tpl₁).publicDepth (tpl₁).chunkDepth)
local notation3 (prettyPrint := false) "fullSize" => packetSize+(2^bundleBits+2^bundleBits)
local notation3 (prettyPrint := false) "fullEmit" => frozenPacketWithBundles (reserve := reserve) schedule G₀ order position σ actual
  count cellNumber vf cf hg short extend (dir₁) number sitePos ownerFits dataArena dataStride dataGap desc gadgets digits ctrl₁ hs hf
  keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes

variable (U deg exteriorBudget : ℕ)
local notation3 (prettyPrint := false) "gateCeiling" => geometryGateCeiling U deg r (lenPred+1)
local notation3 (prettyPrint := false) "order₁" => broadcastOrder (fan schedule) widths ord T
local notation3 (prettyPrint := false) "tab" => reservedGeometryTable aug order₁ fit fullEmit x gateCeiling
local notation3 (prettyPrint := false) "early" => reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
local notation3 (prettyPrint := false) "gap" => 7*(dir₁).candidates
local notation3 (prettyPrint := false) "fresh" => (early).next+gap
local notation3 (prettyPrint := false) "origin" => Allocation.dest fresh reserve (Table.size tab) fullSize packetWidth
local notation3 (prettyPrint := false) "query" => Fintype.card (Board.Physical (pairedTableParameters (lenPred+1) s) pinWidth rw (paid.Entry ⊕ ι))
local notation3 (prettyPrint := false) "guesses" => Fintype.card (Guess (Fin (pairedTableParameters (lenPred+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "ordinary" => SignedTaskArena.withOrdinary basis (fun _ => task₁) early
  (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "routed" => routingExtension (signedBudgetWords rw exteriorBudget)
  dir₁ origin (task₁).cube.cables (task₁).cube.cells
local notation3 (prettyPrint := false) "places" i => reader.frozenTaskPlacement task₁ early i routed
local notation3 (prettyPrint := false) "pinned" i => CubeHeaderInstall.pinFields (places i).extension
  (Allocation.stop fresh reserve (Table.size tab) fullSize packetWidth rw) (task₁).cube.header.d ((task₁).cube.n+1)
  ((task₁).cube.h*(task₁).cube.b) (task₁).cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap (task₁).cube.n (task₁).cube.header.d (task₁).cube.header.blocks (task₁).cube.b (task₁).cube.h (task₁).cube.s)
local notation3 (prettyPrint := false) "first" => freeStartWith physical r 32 64 rw (lenPred+1)
local notation3 (prettyPrint := false) "off" => (early).literal/4
local notation3 (prettyPrint := false) "stripeWidth" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount reserve (Table.size tab) fullSize packetWidth*rw) r
local notation3 (prettyPrint := false) "stripe" => Allocation.stripe fresh reserve (Table.size tab) fullSize packetWidth off stripeWidth
local notation3 (prettyPrint := false) "place₀" => fun i : Fin (R+1) => ReaderPlacement.inArena early
  (places i).valuation (places i).entry (places i).totals (Allocation.fields (pinned i) fresh reserve (Table.size tab) fullSize packetWidth off stripeWidth)
local notation3 (prettyPrint := false) "slot₁" => adviceOffsetWith physical r 32 64 rw (lenPred+1)
local notation3 (prettyPrint := false) "args₁" => fun i : Fin (R+1) => (early).unitAddresses slot₁ (reader.packetAt (place₀ i))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix position signedTag sites edges ports copies ((fan schedule)^T)
  (headerFactor*logWidth r (lenPred+1))
local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
  copies ((fan schedule)^T) headerFactor wireLayout tab task₁ exteriorBudget
local notation3 (prettyPrint := false) "machine" => wiringWith physical P deployed indexWidth link (lenPred+1) ec machineFit
local notation3 (prettyPrint := false) "clockFrame" i => (machine).transferFrame i ((args₁) i).header ((args₁) i).dst
local notation3 (prettyPrint := false) "pl" => privateLayout (early).frame dest (task₁).cube.cables cells J₁ desc dataGap
local notation3 (prettyPrint := false) "portB" => bases dest (task₁).cube.cables cells J₁
local notation3 (prettyPrint := false) "ctlB" => controlsBase dest (task₁).cube.cables cells J₁ live₁
local notation3 (prettyPrint := false) "raw" => SignedTaskArena.rawAddress early (task₁).cube.header.profile (task₁).cube.n (task₁).cube.header.d (task₁).cube.header.cap

local notation "loaded₁" => schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
local notation "birth₁" => max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
local notation "coefficient₁" => (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
local notation "scalar₁" => max (15*loaded₁) (H₁).sites +
  max (max birth₁ (coefficient₁*(loaded₁+1))) (max 1 (15*loaded₁))+1

attribute [local irreducible] Nat.clog Fintype.card Finset.univ

include pw room hook seeds cellPos in
set_option maxHeartbeats 64000000 in
/-- The selected original history emits the packet read by this very deployed
prefix. The physical pin, all 37 controls and the directory scan belong to
the boot family fixed before the exterior was chosen. -/
theorem ChosenReader.deployed_frozen_prefix_publication :
    let «G₀» := tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw)
      (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
    let «tiles» : ℕ := GridHosts.tileCount axes d
    let «w» : ℕ := 60*logWidth r (lenPred+1)
    let «V» : ℕ := CoverScale.sites (Cube D) (d+1)
    let «extent» : ℕ := copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
    let «header» := WorkWords.grouped «V» «extent»
    let «key» := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
    let «fmt» := Boundary.seedFormat «G₀» order position copies
    let «source» := plan.frozenStart «G₀» order position σ
    let «seed₀» := plan.frozenLeaf «G₀» order position W signedTag sites edges ports seedTable x
    let «compiled» := plan.compiled
    let «steps» := («compiled»).tapeSteps «fmt» «header» «key» wr hm
    let «epochFormat» := ProgramSchemas.epoch schedule (d+1) «w» «fmt» T
    let «aug» := PackedHistoryCircuit.compile «steps» T le_rfl (repeatLeaf (fan schedule) «source» T)
    let «base» := (plan.execute «G₀» order position σ).choose
    let «actual» := wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
    let «rTime» : ℕ := TeamContraction.cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
      (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
    let «s₁» := ((packHistory «seed₀» («compiled»).machine.epoch T).term histQ).val
    let «N₀» := (flattenPack T («s₁»).pack).layout
    let «code₁» := ((«compiled»).machine.nativeCode «seed₀» «base» x rfl widths ord fit histQ).val
    let «input₁» := Retained.branch «aug» (broadcastOrder (fan schedule) widths ord T) fit x «code₁»
    let «g₁» : ℕ := inputBlockWidth r (lenPred+1) axes d
    let «p₁» := (⟨R,r,(«actual»).program.length+«rTime»,link,«g₁»,«tiles»⟩ : FieldExport.Params)
    let «hp₁» := (⟨hg,short,gridRoom «actual» Fintype.card_pos⟩ : («p₁»).Valid)
    let «h₁» := attachedHosts «actual» Fintype.card_pos count «N₀»
    let «edge₁» := mergedEdges «p₁» «hp₁» («s₁»).rows.edge
    let «port₁» := (finProdFinEquiv : FreeBlock R «tiles» ≃ Fin ((R+1)*«tiles»)).toEmbedding
    let «finalN» := finalLayout «p₁» «h₁»
    let «scp» := («epochFormat»).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*«tiles») «w»)
    let «desc» : ℕ := seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
      (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «H₁» := boundaryShape schedule (d+1) T
    let «J₁» : ℕ := (fan schedule)^T*«tiles»
    let «live₁» : ℕ := (R+1)*«tiles»
    let «dir₁» := freeDirectory R r ((«actual»).program.length+«rTime») link «tiles» «g₁» «J₁» «desc»
    let «publicDir» := {(«dir₁») with sites := «tiles», entries := «J₁»}
    let «boxes₁» := scheduledBoxes «publicDir» rfl number sitePos
    let «task₁» := hardwareTemplate.withNetwork cells ((«H₁»).edges+(«p₁»).slots)
    let «ctrl₁» := fun i : Fin 37 => (⟨(«task₁»).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
    let «dataArena» : ℕ := («task₁»).cube.cellBank
    let «dataStride» : ℕ := («task₁»).cube.cellStride
    let «dataGap» : ℕ := («task₁»).p.privateGap
    let «hosts₁» := originalDescriptionRows plan.compiled.machine «seed₀» histQ «dir₁» rfl order
    let «livePorts» := Function.Embedding.refl (Fin (R+1) × Fin «tiles»)
    let «final₁» := FinalTies.tieSchema ((«H₁»).edges+(«p₁»).slots) «live₁» packetWidth
    let «priv₁» := FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «reports₁» := FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «tpl₁» := template «scp» «final₁» «boxes₁» hs hf «priv₁» «reports₁»
    let «packetSize» : ℕ := signedGridOutputCount ((«H₁»).edges+4*(R+1)*«tiles») cells «J₁» «live₁»
      37 (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth)
    let «fullSize» : ℕ := «packetSize»+(2^bundleBits+2^bundleBits)
    let «fullEmit» := frozenPacketWithBundles (reserve := reserve) schedule «G₀» order position σ «actual»
      count cellNumber vf cf hg short extend («dir₁») number sitePos ownerFits «dataArena» «dataStride» «dataGap» «desc» gadgets digits «ctrl₁» hs hf
      keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes
    let «gateCeiling» : ℕ := geometryGateCeiling U deg r (lenPred+1)
    let «order₁» := broadcastOrder (fan schedule) widths ord T
    let «tab» := reservedGeometryTable «aug» «order₁» fit «fullEmit» x «gateCeiling»
    let «early» := reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
    let «gap» : ℕ := 7*(«dir₁»).candidates
    let «fresh» : ℕ := («early»).next+«gap»
    let «origin» : ℕ := Allocation.dest «fresh» reserve (Table.size «tab») «fullSize» packetWidth
    let «routed» := routingExtension (signedBudgetWords rw exteriorBudget)
      «dir₁» «origin» («task₁»).cube.cables («task₁»).cube.cells
    let «places» := fun i : Fin (R+1) => reader.frozenTaskPlacement «task₁» «early» i «routed»
    let «pinned» := fun i : Fin (R+1) => CubeHeaderInstall.pinFields («places» i).extension
      (Allocation.stop «fresh» reserve (Table.size «tab») «fullSize» packetWidth rw) («task₁»).cube.header.d ((«task₁»).cube.n+1)
      ((«task₁»).cube.h*(«task₁»).cube.b) («task₁»).cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.blocks («task₁»).cube.b («task₁»).cube.h («task₁»).cube.s)
    let «first» : ℕ := freeStartWith physical r 32 64 rw (lenPred+1)
    let «off» : ℕ := («early»).literal/4
    let «stripeWidth» : ℕ := GeometryAdviceRate.stripeWidth
      (GeometryOutput.packetCount reserve (Table.size «tab») «fullSize» packetWidth*rw) r
    let «stripe» := Allocation.stripe «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»
    let «place₀» := fun i : Fin (R+1) => ReaderPlacement.inArena «early»
      («places» i).valuation («places» i).entry («places» i).totals (Allocation.fields («pinned» i) «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»)
    let «slot₁» : ℕ := adviceOffsetWith physical r 32 64 rw (lenPred+1)
    let «args₁» := fun i : Fin (R+1) => («early»).unitAddresses «slot₁» (reader.packetAt («place₀» i))
    let «deployed» := reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
      copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget
    let «machine» := wiringWith physical P «deployed» indexWidth link (lenPred+1) ec machineFit
    let «clockFrame» := fun i : Fin (R+1) => («machine»).transferFrame i ((«args₁») i).header ((«args₁») i).dst
    let «pl» := privateLayout («early»).frame dest («task₁»).cube.cables cells «J₁» «desc» «dataGap»
    let «portB» := bases dest («task₁»).cube.cables cells «J₁»
    let «ctlB» : ℕ := controlsBase dest («task₁»).cube.cables cells «J₁» «live₁»
    let «loaded₁» : ℕ := schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
    let «birth₁» : ℕ := max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «coefficient₁» : ℕ := (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
    let «scalar₁» : ℕ := max (15*«loaded₁») («H₁»).sites +
      max (max «birth₁» («coefficient₁»*(«loaded₁»+1))) (max 1 (15*«loaded₁»))+1
    ∀ {slope power coeff : ℕ}
    (_digitsChoice : digits=packetWidth)
    (_capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=paid))
    (_inputBounds : SignedPacketInputBounds schedule (d+1) T cells «live₁» «w» packetWidth slope power coeff gadgets «fmt» «publicDir» rfl number)
    (_numerals : FrozenPacketNumerals paid number gadgets hdr packetWidth «scalar₁» «loaded₁»)
    (_packetAddress : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth packetWidth<2^packetWidth)
    (_gateFit : (geometryTable «aug» «order₁» fit «fullEmit» x).size≤«gateCeiling»)
    (_geometryDest : Allocation.dest «fresh» reserve «gateCeiling» «fullSize» packetWidth=dest)
    (_headerWidth : wireLayout.header=JointHeader.PositiveFields.width reserve («task₁»).cube.n («task₁»).cube.header.d
      («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (fixed : Routing.Block (R+1))
    (regions : JointRoom «dir₁» «first» a (signedBootStripe «first») «stripe»)
    (copiesFit : reader.packetBitCount≤r)
    (_wfit : packetWidth≤rw)
    (_endFits : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth rw<2^rw)
    (memFit : («early»).next<2^rw)
    (hw : 0<rw)
    (threeTeams : 2<R+1)
    (hdrPos : 0<wireLayout.header)
    (cap : wireLayout.header≤r*link)
    (clock : ∀ u,packetUnitBudget ((«args₁») u).advice.count rw («clockFrame» u)
      ((«machine»).pinLayout u ((«args₁») u).ibase ((«args₁») u).hbase ((«args₁») u).starbase)≤basis.limit.val)
    (p : JointHeader.PositiveFields reserve («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (pin : Fin indexWidth → Bool)
    (ex : {z // PositiveExterior «machine» «args₁» pin rw z})
    (_common : ∀ b, JointHeader.observed wireLayout ex.val b=p.bits)
    (_encoded : «code₁»=p.profile)
    (bufferExtent : ℕ)
    (_budgetFits : exteriorBudget<2^rw)
    (_room₀ : («task₁»).cube.stop<2^rw)
    (_cellsFit : cells≤2^rw)
    (_span : («early»).next+7*(«dir₁»).candidates≤dest)
    (_rawRoom : («early»).next+7*(«dir₁»).candidates≤(«task₁»).cube.header.header)
    (_rs : r≤«tiles»)
    (_posR : 0<r)
    (_positiveTail : 0<((«actual»).program.length+«rTime»)/2)
    (_privateTail : «J₁»*«desc»≤(R+1)*r*(((«actual»).program.length+«rTime»)/2))
    (_localRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+(∑ j,if cells₁ («hosts₁» j)=c then «desc» else 0)≤(«task₁»).cube.cellStride)
    (_globalRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+«J₁»*«desc»≤bufferExtent)
    (_ctl : «ctlB»+8<2^rw)
    (_wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound («dir₁») («pl»).raw («portB»).livePairs bufferExtent)<2^rw),
    let chosen := reader.deployedFrozenSites_boots physical P basis machineFit W position sites edges ports copies
      ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock
    let nodes := chosen.2.choose pin ex
    ∀ (u : Fin (R+1)) (g : Fin (nodes u).start.guessWidth → Bool),
      let pk := reader.packetAt («place₀» u)
      let node := nodes u
      let lib := install SparseExterior.driver (lenPred+1) node.start.routines
      let pub := («deployed»).publicWords u
      let bank := («deployed»).registers u
      let op := («early»).operands u «slot₁» pk
      let ad := («args₁») u
      let fs := («machine»).processorFields u pin ex.val ad.ibase ad.hbase ad.starbase
      let init := processorMemory fs rw
      let bc := («machine»).transferFrame u ad.header ad.dst
      let time := jointBudget pk.bits.length rw+bc.readTicks+2+((pinSetup.slots+17*op.layout.count+1)+
        GeometryAdviceRate.ticks («tab»).size reserve «fullSize» packetWidth rw)
      ∃ ret : Returns (withStartup pinGeometry) pub lib bank init,
        ProfilePaths (withStartup pinGeometry) node.start.guessWidth pub lib bank init True time «origin»
          (emittedWords «aug» «order₁» fit «fullEmit» x «code₁») (BootResidence (F:=fs) «early» u «slot₁» pk bc ad.advice pub lib p.bits init bank) ∧
        ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn g ∧
        PublishedPin «task₁» «dir₁» «finalN» cells₁ «edge₁» «port₁» «hosts₁» «livePorts» «early» u «slot₁» pk «origin» «dataGap» bc p.bits fs
          pub lib g (node.pins g).val.2.1 (node.pins g).val.2.2 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins g).val.1) (traceCost ret.val.1) ∧
        Image F₂ ((«s₁»).rows.site ∘ «hosts₁») («port₁» ∘ «livePorts» ∘ finProdFinEquiv.symm)
          ((source₂).eval «input₁») «origin» (readings ret.val.2.2) ∧
        ∀ j : Fin 37, readings ret.val.2.2 (controlsBase «origin» («task₁»).cube.cables cells «J₁» «live₁»+j.val)=(«task₁»).controls j.val := by
  intro «G₀» «tiles» «w» «V» «extent» «header» «key» «fmt» «source» «seed₀» «compiled» «steps» «epochFormat» «aug» «base»
    «actual» «rTime» «s₁» «N₀» «code₁» «input₁» «g₁» «p₁» «hp₁» «h₁» «edge₁» «port₁» «finalN» «scp» «desc» «H₁» «J₁»
    «live₁» «dir₁» «publicDir» «boxes₁» «task₁» «ctrl₁» «dataArena» «dataStride» «dataGap» «hosts₁» «livePorts»
    «final₁» «priv₁» «reports₁» «tpl₁» «packetSize» «fullSize» «fullEmit» «gateCeiling» «order₁» «tab» «early» «gap»
    «fresh» «origin» «routed» «places» «pinned» «first» «off» «stripeWidth» «stripe» «place₀» «slot₁» «args₁»
    «deployed» «machine» «clockFrame» «pl» «portB» «ctlB» «loaded₁» «birth₁» «coefficient₁» «scalar₁» slope power
    coeff digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions
    copiesFit wfit endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀
    cellsFit span rawRoom rs posR positiveTail privateTail localRoom globalRoom ctl wordRoom chosen nodes u g pk node
    lib pub bank op ad fs init bc time
  have size : («tab»).size=gateCeiling := (geometryTable «aug» «order₁» fit «fullEmit» x).reserve_size «gateCeiling» gateFit
  have orig : «origin»=dest := (congrArg (fun boundGates => Allocation.dest «fresh» reserve boundGates
    «fullSize» packetWidth) size).trans geometryDest
  have bound := reader.deployedFrozenSites_publication physical P basis machineFit W position sites edges ports
    copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget u budgetFits
  obtain ⟨pubEq,installed,_⟩ := bound
  let publicAt := fun bankAddress => ((«early»).operands u «slot₁» pk).bank (core
    (withDemandBase ((«task₁»).routeBank («early»).frame ((ordinary).publicWords u)) («early»).next)
    bankAddress («task₁»).cube.cables cells)
  have publicAtDest := pubEq.trans (congrArg publicAt orig)
  let fieldsAt := fun bankAddress gates => signedProfileExtension «task₁» (signedBudgetWords rw exteriorBudget) «dir₁»
    bankAddress («task₁»).cube.cables cells raw u.val rw «fresh» reserve gates «fullSize» packetWidth «off» «stripeWidth»
  have fieldsAtDest := installed.trans (congrArg₂ fieldsAt orig size)
  have grid := (plan.frozen_leaf_installed «G₀» order position W signedTag sites edges ports seedTable x).trans
    (SewnTape.native_grid_installed order position physical P basis machineFit)
  let wire : HeaderExterior wireLayout p.bits := ⟨ex.val,common⟩
  have original := plan.frozen_chosen_publication «G₀» order position W
    signedTag sites edges ports seedTable x wr hm seeds number widths ord fit «actual» count cellNumber vf cf hg short pw
    extend room hook histQ hardwareTemplate «desc» sitePos cellPos ownerFits gadgets digits ctrlFit hs hf keyFits sitesFit
    keysFit sw pad dest hdr bankLayout bundleBits shapes reader physical P ordinary machineFit (fun u => («places» u).valuation)
    (fun u => («places» u).entry) (fun u => («places» u).totals) (fun u => «pinned» u) wireLayout «gateCeiling»
    (signedBootStripe «first») (fun _ => []) strings p SparseExterior.driver ((ordinary).publicWords u)
    (signedBudgetWords rw exteriorBudget) raw u.val rw bufferExtent digitsChoice capChoice inputBounds numerals grid
    packetAddress gateFit geometryDest
    (p.bits_length.trans headerWidth.symm) wire u pin regions copiesFit wfit endFits encoded rfl node g publicAtDest fieldsAtDest
    room₀ cellsFit span rawRoom rs posR positiveTail privateTail localRoom globalRoom ctl wordRoom
  let oldOp := reader.siteOperandsWith physical P ordinary «place₀» machineFit wireLayout.header u
  have operands : oldOp=op := reader.siteOperands_arenaWith physical P ordinary machineFit
    (fun i => («places» i).valuation) (fun i => («places» i).entry) (fun i => («places» i).totals)
    (fun i => Allocation.fields («pinned» i) «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth») wireLayout u
  let ticks := fun count gates => jointBudget pk.bits.length rw+bc.readTicks+2+
    ((pinSetup.slots+17*count+1)+GeometryAdviceRate.ticks gates reserve «fullSize» packetWidth rw)
  have timeEq : ticks oldOp.layout.count «gateCeiling»=time :=
    congrArg₂ ticks (congrArg (fun p : PacketOperands => p.layout.count) operands) size.symm
  have siteEq : «deployed» = _ := reader.deployedFrozenSites_eq_startup physical P basis machineFit W position sites
    edges ports copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget
  let wired := fun teamSite : SiteData R r 64 32 rw a => wiringWith physical P teamSite indexWidth link (lenPred+1) ec machineFit
  have rawWire := (congrArg wired siteEq).symm
  have atPub := (congrArg (fun teamSite : SiteData R r 64 32 rw a => teamSite.publicWords u) siteEq).symm
  have atBank := (congrArg (fun teamSite : SiteData R r 64 32 rw a => teamSite.registers u) siteEq).symm
  have atMac := node.installed_routines_at
  have atMem := Wiring.processorMemory_at («w»:=rw) u pin ex.val rawWire
    oldOp.layout.ibase oldOp.layout.hbase oldOp.layout.starbase ad.ibase ad.hbase ad.starbase
  have packetFacts := original.choose_spec
  let returned := packetFacts.2.2.choose
  have run := packetFacts.2.2.choose_spec
  exact published_pin_at_native_inputs «task₁» «dir₁» «finalN» cells₁ «edge₁» «port₁» «hosts₁» «livePorts» «early» u «slot₁» pk «dataGap»
    bc p.bits pub lib init bank g (node.pins g).val.2.1 (node.pins g).val.2.2 (node.used+traceCost (node.pins g).val.1)
    (fs:=fs) packetFacts.1 orig.symm timeEq (congrArg PacketOperands.advice operands)
    (emittedWords «aug» «order₁» fit «fullEmit» x «code₁») atPub atMac atBank atMem
    packetFacts.2.1 returned run.1 run.2.2.2.2.1 («s₁»).rows.site F₂ ((source₂).eval «input₁»)
    run.2.2.2.2.2.1 run.2.2.2.1

open RoutingISA.Evaluator.ScheduleClock JointHeader Cube.Physical

include pw room hook seeds cellPos in
set_option maxHeartbeats 12800000 in
/-- The jointly returning pin pays for its native geometry, directory, signed writer
and transfer on the deployed receiver of the authenticated frozen history. -/
theorem ChosenReader.deployed_frozen_prefix_early :
    let «G₀» := tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw)
      (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
    let «tiles» : ℕ := GridHosts.tileCount axes d
    let «w» : ℕ := 60*logWidth r (lenPred+1)
    let «V» : ℕ := CoverScale.sites (Cube D) (d+1)
    let «extent» : ℕ := copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
    let «header» := WorkWords.grouped «V» «extent»
    let «key» := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
    let «fmt» := Boundary.seedFormat «G₀» order position copies
    let «source» := plan.frozenStart «G₀» order position σ
    let «seed₀» := plan.frozenLeaf «G₀» order position W signedTag sites edges ports seedTable x
    let «compiled» := plan.compiled
    let «steps» := («compiled»).tapeSteps «fmt» «header» «key» wr hm
    let «epochFormat» := ProgramSchemas.epoch schedule (d+1) «w» «fmt» T
    let «aug» := PackedHistoryCircuit.compile «steps» T le_rfl (repeatLeaf (fan schedule) «source» T)
    let «base» := (plan.execute «G₀» order position σ).choose
    let «actual» := wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
    let «rTime» : ℕ := TeamContraction.cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
      (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
    let «s₁» := ((packHistory «seed₀» («compiled»).machine.epoch T).term histQ).val
    let «N₀» := (flattenPack T («s₁»).pack).layout
    let «code₁» := ((«compiled»).machine.nativeCode «seed₀» «base» x rfl widths ord fit histQ).val
    let «g₁» : ℕ := inputBlockWidth r (lenPred+1) axes d
    let «p₁» := (⟨R,r,(«actual»).program.length+«rTime»,link,«g₁»,«tiles»⟩ : FieldExport.Params)
    let «hp₁» := (⟨hg,short,gridRoom «actual» Fintype.card_pos⟩ : («p₁»).Valid)
    let «h₁» := attachedHosts «actual» Fintype.card_pos count «N₀»
    let «edge₁» := mergedEdges «p₁» «hp₁» («s₁»).rows.edge
    let «port₁» := (finProdFinEquiv : FreeBlock R «tiles» ≃ Fin ((R+1)*«tiles»)).toEmbedding
    let «finalN» := finalLayout «p₁» «h₁»
    let «scp» := («epochFormat»).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*«tiles») «w»)
    let «desc» : ℕ := seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
      (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «H₁» := boundaryShape schedule (d+1) T
    let «J₁» : ℕ := (fan schedule)^T*«tiles»
    let «live₁» : ℕ := (R+1)*«tiles»
    let «dir₁» := freeDirectory R r ((«actual»).program.length+«rTime») link «tiles» «g₁» «J₁» «desc»
    let «publicDir» := {(«dir₁») with sites := «tiles», entries := «J₁»}
    let «boxes₁» := scheduledBoxes «publicDir» rfl number sitePos
    let «task₁» := hardwareTemplate.withNetwork cells ((«H₁»).edges+(«p₁»).slots)
    let «ctrl₁» := fun i : Fin 37 => (⟨(«task₁»).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
    let «dataArena» : ℕ := («task₁»).cube.cellBank
    let «dataStride» : ℕ := («task₁»).cube.cellStride
    let «dataGap» : ℕ := («task₁»).p.privateGap
    let «hosts₁» := originalDescriptionRows plan.compiled.machine «seed₀» histQ «dir₁» rfl order
    let «livePorts» := Function.Embedding.refl (Fin (R+1) × Fin «tiles»)
    let «final₁» := FinalTies.tieSchema ((«H₁»).edges+(«p₁»).slots) «live₁» packetWidth
    let «priv₁» := FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «reports₁» := FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «tpl₁» := template «scp» «final₁» «boxes₁» hs hf «priv₁» «reports₁»
    let «packetSize» : ℕ := signedGridOutputCount ((«H₁»).edges+4*(R+1)*«tiles») cells «J₁» «live₁»
      37 (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth)
    let «fullSize» : ℕ := «packetSize»+(2^bundleBits+2^bundleBits)
    let «fullEmit» := frozenPacketWithBundles (reserve := reserve) schedule «G₀» order position σ «actual»
      count cellNumber vf cf hg short extend («dir₁») number sitePos ownerFits «dataArena» «dataStride» «dataGap» «desc» gadgets digits «ctrl₁» hs hf
      keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes
    let «gateCeiling» : ℕ := geometryGateCeiling U deg r (lenPred+1)
    let «order₁» := broadcastOrder (fan schedule) widths ord T
    let «tab» := reservedGeometryTable «aug» «order₁» fit «fullEmit» x «gateCeiling»
    ∀ (siteTable : Table (Fin reserve ⊕ Fin 0) «fullSize» packetWidth) (_ : siteTable=«tab»)
      (siteTask : SignedTaskArena.Layout) (_ : siteTask=«task₁»),
    let «early» := reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
    let «gap» : ℕ := 7*(«dir₁»).candidates
    let «fresh» : ℕ := («early»).next+«gap»
    let «origin» : ℕ := Allocation.dest «fresh» reserve (Table.size siteTable) «fullSize» packetWidth
    let «routed» := routingExtension (signedBudgetWords rw exteriorBudget)
      «dir₁» «origin» (siteTask).cube.cables (siteTask).cube.cells
    let «places» := fun i : Fin (R+1) => reader.frozenTaskPlacement siteTask «early» i «routed»
    let «pinned» := fun i : Fin (R+1) => CubeHeaderInstall.pinFields («places» i).extension
      (Allocation.stop «fresh» reserve (Table.size siteTable) «fullSize» packetWidth rw) (siteTask).cube.header.d ((siteTask).cube.n+1)
      ((siteTask).cube.h*(siteTask).cube.b) (siteTask).cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap (siteTask).cube.n (siteTask).cube.header.d (siteTask).cube.header.blocks (siteTask).cube.b (siteTask).cube.h (siteTask).cube.s)
    let «first» : ℕ := freeStartWith physical r 32 64 rw (lenPred+1)
    let «off» : ℕ := («early»).literal/4
    let «stripeWidth» : ℕ := GeometryAdviceRate.stripeWidth
      (GeometryOutput.packetCount reserve (Table.size siteTable) «fullSize» packetWidth*rw) r
    let «stripe» := Allocation.stripe «fresh» reserve (Table.size siteTable) «fullSize» packetWidth «off» «stripeWidth»
    let «place₀» := fun i : Fin (R+1) => ReaderPlacement.inArena «early»
      («places» i).valuation («places» i).entry («places» i).totals (Allocation.fields («pinned» i) «fresh» reserve (Table.size siteTable) «fullSize» packetWidth «off» «stripeWidth»)
    let «slot₁» : ℕ := adviceOffsetWith physical r 32 64 rw (lenPred+1)
    let «args₁» := fun i : Fin (R+1) => («early»).unitAddresses «slot₁» (reader.packetAt («place₀» i))
    let «deployed» := reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
      copies ((fan schedule)^T) headerFactor wireLayout siteTable siteTask exteriorBudget
    let «machine» := wiringWith physical P «deployed» indexWidth link (lenPred+1) ec machineFit
    let «clockFrame» := fun i : Fin (R+1) => («machine»).transferFrame i ((«args₁») i).header ((«args₁») i).dst
    let «pl» := privateLayout («early»).frame dest (siteTask).cube.cables cells «J₁» «desc» «dataGap»
    let «portB» := bases dest (siteTask).cube.cables cells «J₁»
    let «ctlB» : ℕ := controlsBase dest (siteTask).cube.cables cells «J₁» «live₁»
    let «loaded₁» : ℕ := schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
    let «birth₁» : ℕ := max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «coefficient₁» : ℕ := (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
    let «scalar₁» : ℕ := max (15*«loaded₁») («H₁»).sites +
      max (max «birth₁» («coefficient₁»*(«loaded₁»+1))) (max 1 (15*«loaded₁»))+1
    ∀ {slope power coeff : ℕ}
    (_digitsChoice : digits=packetWidth)
    (_capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=paid))
    (_inputBounds : SignedPacketInputBounds schedule (d+1) T cells «live₁» «w» packetWidth slope power coeff gadgets «fmt» «publicDir» rfl number)
    (_numerals : FrozenPacketNumerals paid number gadgets hdr packetWidth «scalar₁» «loaded₁»)
    (_packetAddress : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth packetWidth<2^packetWidth)
    (_gateFit : (geometryTable «aug» «order₁» fit «fullEmit» x).size≤«gateCeiling»)
    (_geometryDest : Allocation.dest «fresh» reserve «gateCeiling» «fullSize» packetWidth=dest)
    (_headerWidth : wireLayout.header=JointHeader.PositiveFields.width reserve (siteTask).cube.n (siteTask).cube.header.d
      (siteTask).cube.header.cap (R+1) (siteTask).dim rw)
    (fixed : Routing.Block (R+1))
    (regions : JointRoom «dir₁» «first» a (signedBootStripe «first») «stripe»)
    (copiesFit : reader.packetBitCount≤r)
    (_wfit : packetWidth≤rw)
    (_endFits : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth rw<2^rw)
    (memFit : («early»).next<2^rw)
    (hw : 0<rw)
    (threeTeams : 2<R+1)
    (hdrPos : 0<wireLayout.header)
    (cap : wireLayout.header≤r*link)
    (clock : ∀ u,packetUnitBudget ((«args₁») u).advice.count rw («clockFrame» u)
      ((«machine»).pinLayout u ((«args₁») u).ibase ((«args₁») u).hbase ((«args₁») u).starbase)≤basis.limit.val)
    (p : JointHeader.PositiveFields reserve (siteTask).cube.n (siteTask).cube.header.d (siteTask).cube.header.cap (R+1) (siteTask).dim rw)
    (pin : Fin indexWidth → Bool)
    (ex : {z // PositiveExterior «machine» «args₁» pin rw z})
    (_common : ∀ b, JointHeader.observed wireLayout ex.val b=p.bits)
    (_encoded : «code₁»=p.profile)
    (bufferExtent : ℕ)
    (_budgetFits : exteriorBudget<2^rw)
    (_room₀ : (siteTask).cube.stop<2^rw)
    (_cellsFit : cells≤2^rw)
    (_span : («early»).next+7*(«dir₁»).candidates≤dest)
    (_rawRoom : («early»).next+7*(«dir₁»).candidates≤(siteTask).cube.header.header)
    (_rs : r≤«tiles»)
    (_posR : 0<r)
    (_positiveTail : 0<((«actual»).program.length+«rTime»)/2)
    (_privateTail : «J₁»*«desc»≤(R+1)*r*(((«actual»).program.length+«rTime»)/2))
    (_localRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+(∑ j,if cells₁ («hosts₁» j)=c then «desc» else 0)≤(siteTask).cube.cellStride)
    (_globalRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+«J₁»*«desc»≤bufferExtent)
    (_ctl : «ctlB»+8<2^rw)
    (_wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound («dir₁») («pl»).raw («portB»).livePairs bufferExtent)<2^rw)
    (_shortDescription : «desc»≤(«dir₁»).literal)
    (_enoughTeams : (siteTask).cube.teams=R+1)
    (_guard : SelectedRawWriterRoom (siteTask).cube «dir₁» rw exteriorBudget («early»).next reserve (siteTable).size «fullSize» packetWidth)
    (_traffic : intercellWidth «finalN» cells₁≤2*(«dir₁»).teams*exteriorBudget)
    {α ξ : ℝ}
    (_route : RouteTableInputs (siteTask).cube «dir₁» α ξ (lenPred+1) rw («early»).frame link)
    (_budgetEq : exteriorBudget=TeamScales.exterior ξ r (lenPred+1))
    (_literalBound : («early»).literal≤TeamScales.literal α (lenPred+1))
    (_headerBound : (wireLayout.header:ℝ)≤r*((lenPred+1:ℕ):ℝ)^(24/25:ℝ))
    (_bound : RoutingISA.Evaluator.ScheduleClock.CoreAt α ξ (lenPred+1))
    (budget : PhaseCharges)
    (_window : ∀ after : ℕ → ℕ, let layout := Cube.LabelIndex.layout («early»).frame after
      let ar := (siteTask).cube
      let rows := NativeDemands.rows «finalN» cells₁ «edge₁» «port₁» «dir₁» «hosts₁» «livePorts» «dataGap»
      let axis := Fin.ofNat (ar.n+1) (Cube.Physical.readCode (ar.n+1) p.cube.1)
      layout.cells=ar.cells → layout.cableCount=ar.cables → layout.deliveryCount=rows.length → layout.labels=ar.alphabet →
      2048*(exteriorBudget+(R+1+1)^3+(rows.length+ar.header.d.choose 2)+r+1)≤budget.core ∧
        GeometryAdviceRate.ticks (siteTable).size reserve «fullSize» packetWidth rw+
          ScheduleClock.beforeDirectory (R+1) («dir₁»).sites («dir₁»).entries+
          ScheduleClock.rawScheduleTicks ar («early»).frame («early»).broadcastBase axis.val R rows.length after≤budget.before),
    let chosen := reader.deployedFrozenSites_boots physical P basis machineFit W position sites edges ports copies
      ((fan schedule)^T) headerFactor wireLayout siteTable siteTask exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock
    let nodes := chosen.2.choose pin ex
    ∀ (tuple : PinStart.JointPrefix (siteTask).id (fun u => (nodes u).start)) (u : Fin (R+1)),
      let v := PinStart.visits (siteTask).id (fun u => (nodes u).start) (tuple u)
      (nodes u).used+traceCost ((nodes u).pins (tuple u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1≤
        budget.core+budget.before := by
  intro «G₀» «tiles» «w» «V» «extent» «header» «key» «fmt» «source» «seed₀» «compiled» «steps» «epochFormat» «aug» «base»
    «actual» «rTime» «s₁» «N₀» «code₁» «g₁» «p₁» «hp₁» «h₁» «edge₁» «port₁» «finalN» «scp» «desc» «H₁» «J₁» «live₁»
    «dir₁» «publicDir» «boxes₁» «task₁» «ctrl₁» «dataArena» «dataStride» «dataGap» «hosts₁» «livePorts» «final₁»
    «priv₁» «reports₁» «tpl₁» «packetSize» «fullSize» «fullEmit» «gateCeiling» «order₁» «tab» siteTable sameTable siteTask sameTask
  subst siteTable siteTask
  intro «early» «gap» «fresh»
    «origin» «routed» «places» «pinned» «first» «off» «stripeWidth» «stripe» «place₀» «slot₁» «args₁» «deployed»
    «machine» «clockFrame» «pl» «portB» «ctlB» «loaded₁» «birth₁» «coefficient₁» «scalar₁» slope power coeff
    digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit
    wfit endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit
    span rawRoom rs posR positiveTail privateTail localRoom globalRoom ctl wordRoom shortDescription enoughTeams guard
    traffic α ξ route budgetEq literalBound headerBound bound budget window chosen nodes tuple
  let packageOn := reader.deployed_frozen_prefix_publication (physical:=physical) (P:=P) (basis:=basis) (machineFit:=machineFit) (W:=W) (position:=position)
    (sites:=sites) (edges:=edges) (ports:=ports) (plan:=plan) (wireLayout:=wireLayout) (x:=x) (seedTable:=seedTable)
    (wr:=wr) (hm:=hm) (seeds:=seeds) (number:=number) (widths:=widths) (ord:=ord) (fit:=fit) (count:=count)
    (cellNumber:=cellNumber) (vf:=vf) (cf:=cf) (hg:=hg) (short:=short) (pw:=pw) (extend:=extend) (room:=room)
    (hook:=hook) (histQ:=histQ) (hardwareTemplate:=hardwareTemplate) (sitePos:=sitePos) (cellPos:=cellPos)
    (ownerFits:=ownerFits) (gadgets:=gadgets) (digits:=digits) (ctrlFit:=ctrlFit) (hs:=hs) (hf:=hf) (keyFits:=keyFits)
    (sitesFit:=sitesFit) (keysFit:=keysFit) (sw:=sw) (pad:=pad) (dest:=dest) (hdr:=hdr) (bankLayout:=bankLayout)
    (bundleBits:=bundleBits) (shapes:=shapes) (U:=U) (deg:=deg) (exteriorBudget:=exteriorBudget)
    digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit wfit
    endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit span rawRoom
    rs posR positiveTail privateTail localRoom globalRoom ctl wordRoom
  have grid := (plan.frozen_leaf_installed «G₀» order position W signedTag sites edges ports seedTable x).trans
    (SewnTape.native_grid_installed order position physical P basis machineFit)
  have sizeFit := (plan.frozen_packet_operands «G₀» order position W signedTag sites edges ports seedTable x wr hm seeds number widths ord fit
    «actual» count cellNumber vf cf hg short pw extend room hook histQ «dir₁» sitePos cellPos
    «dataArena» «dataStride» «dataGap» «desc» gadgets digits hs hf dest hdr
    digitsChoice capChoice rfl inputBounds numerals grid «fresh» «gateCeiling» bundleBits geometryDest packetAddress).1
  have net := (plan.frozen_signed_packet_geometry «G₀» order position W signedTag sites edges ports seedTable x wr hm seeds number
    widths ord fit «actual» count cellNumber vf cf hg short pw extend room hook histQ).2.1
  have realBounds : («dir₁»).DestinationBounds := by
    refine ⟨positiveTail,hg,posR,le_rfl,?_⟩
    simpa only [«dir₁»,«rTime»,«g₁»,freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
      gridRoom «actual» (show 0<«tiles» from Fintype.card_pos)
  have limits := guard.located_writer_fields (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth) bundleBits rfl shortDescription
  have headerSize := (congrArg List.length p.bits_eq_emitted).symm.trans (p.bits_length.trans headerWidth.symm)
  apply reader.deployed_joint_prefix_early physical P basis machineFit W position sites edges ports copies ((fan schedule)^T)
    headerFactor wireLayout «tab» «task₁» exteriorBudget (List.ofFn p.profile) (DiagonalTallyRAM.broadcast rw p.rawCounts) 0 p.cube
    «finalN» cells₁ (fun v => (rawState v).program.size) («s₁»).rows.site «edge₁» «port₁» F₂ «hosts₁» «livePorts»
    (fun _ => rfl) realBounds fixed regions copiesFit memFit hw threeTeams hdrPos cap clock pin ex tuple net (fun _ => rfl)
    sizeFit ownerFits wfit cellPos privateTail (List.length_ofFn ..) headerSize (Nat.le_trans (Nat.add_le_add_left (by decide : 28≤37) _) limits.1)
    limits.2 enoughTeams posR guard traffic route budgetEq literalBound headerBound bound budget window
  intro i
  obtain ⟨ret,paths,digits,published,image,controls⟩ := packageOn i (tuple i).1
  have heads := published_return_at_header p.bits_eq_emitted paths published
  exact ⟨«origin»,emittedWords «aug» «order₁» fit «fullEmit» x «code₁»,ret,heads.1,digits,heads.2,image,controls⟩

open PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan Cube.MeanChoice Cube.Tally
open Directory.PrivateBank CellAddressPhysical TeamContraction.JointHeader RoutingISA.LocalRow
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

include pw room hook seeds cellPos in
set_option maxHeartbeats 25600000 in
/-- The bare site for one selected frozen history and arbitrary physical pin digits.
It retains its actual profile runtime, emitted words and directory publication
on the very same packet and memory used by the selected raw writer. -/
theorem ChosenReader.deployed_frozen_raw_publication :
    let «G₀» := tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw)
      (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
    let «tiles» : ℕ := GridHosts.tileCount axes d
    let «w» : ℕ := 60*logWidth r (lenPred+1)
    let «V» : ℕ := CoverScale.sites (Cube D) (d+1)
    let «extent» : ℕ := copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
    let «header» := WorkWords.grouped «V» «extent»
    let «key» := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
    let «fmt» := Boundary.seedFormat «G₀» order position copies
    let «source» := plan.frozenStart «G₀» order position σ
    let «seed₀» := plan.frozenLeaf «G₀» order position W signedTag sites edges ports seedTable x
    let «compiled» := plan.compiled
    let «steps» := («compiled»).tapeSteps «fmt» «header» «key» wr hm
    let «epochFormat» := ProgramSchemas.epoch schedule (d+1) «w» «fmt» T
    let «aug» := PackedHistoryCircuit.compile «steps» T le_rfl (repeatLeaf (fan schedule) «source» T)
    let «base» := (plan.execute «G₀» order position σ).choose
    let «actual» := wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
    let «rTime» : ℕ := TeamContraction.cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
      (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
    let «s₁» := ((packHistory «seed₀» («compiled»).machine.epoch T).term histQ).val
    let «N₀» := (flattenPack T («s₁»).pack).layout
    let «code₁» := ((«compiled»).machine.nativeCode «seed₀» «base» x rfl widths ord fit histQ).val
    let «g₁» : ℕ := inputBlockWidth r (lenPred+1) axes d
    let «p₁» := (⟨R,r,(«actual»).program.length+«rTime»,link,«g₁»,«tiles»⟩ : FieldExport.Params)
    let «h₁» := attachedHosts «actual» Fintype.card_pos count «N₀»
    let «finalN» := finalLayout «p₁» «h₁»
    let «scp» := («epochFormat»).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*«tiles») «w»)
    let «desc» : ℕ := seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
      (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «H₁» := boundaryShape schedule (d+1) T
    let «J₁» : ℕ := (fan schedule)^T*«tiles»
    let «live₁» : ℕ := (R+1)*«tiles»
    let «dir₁» := freeDirectory R r ((«actual»).program.length+«rTime») link «tiles» «g₁» «J₁» «desc»
    let «publicDir» := {(«dir₁») with sites := «tiles», entries := «J₁»}
    let «boxes₁» := scheduledBoxes «publicDir» rfl number sitePos
    let «task₁» := hardwareTemplate.withNetwork cells ((«H₁»).edges+(«p₁»).slots)
    let «ctrl₁» := fun i : Fin 37 => (⟨(«task₁»).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
    let «dataArena» : ℕ := («task₁»).cube.cellBank
    let «dataStride» : ℕ := («task₁»).cube.cellStride
    let «dataGap» : ℕ := («task₁»).p.privateGap
    let «hosts₁» := originalDescriptionRows plan.compiled.machine «seed₀» histQ «dir₁» rfl order
    let «final₁» := FinalTies.tieSchema ((«H₁»).edges+(«p₁»).slots) «live₁» packetWidth
    let «priv₁» := FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «reports₁» := FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «tpl₁» := template «scp» «final₁» «boxes₁» hs hf «priv₁» «reports₁»
    let «packetSize» : ℕ := signedGridOutputCount ((«H₁»).edges+4*(R+1)*«tiles») cells «J₁» «live₁»
      37 (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth)
    let «fullSize» : ℕ := «packetSize»+(2^bundleBits+2^bundleBits)
    let «fullEmit» := frozenPacketWithBundles (reserve := reserve) schedule «G₀» order position σ «actual»
      count cellNumber vf cf hg short extend («dir₁») number sitePos ownerFits «dataArena» «dataStride» «dataGap» «desc» gadgets digits «ctrl₁» hs hf
      keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes
    let «gateCeiling» : ℕ := geometryGateCeiling U deg r (lenPred+1)
    let «order₁» := broadcastOrder (fan schedule) widths ord T
    let «tab» := reservedGeometryTable «aug» «order₁» fit «fullEmit» x «gateCeiling»
    let «early» := reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
    let «gap» : ℕ := 7*(«dir₁»).candidates
    let «fresh» : ℕ := («early»).next+«gap»
    let «origin» : ℕ := Allocation.dest «fresh» reserve (Table.size «tab») «fullSize» packetWidth
    let «routed» := routingExtension (signedBudgetWords rw exteriorBudget)
      «dir₁» «origin» («task₁»).cube.cables («task₁»).cube.cells
    let «places» := fun i : Fin (R+1) => reader.frozenTaskPlacement «task₁» «early» i «routed»
    let «pinned» := fun i : Fin (R+1) => CubeHeaderInstall.pinFields («places» i).extension
      (Allocation.stop «fresh» reserve (Table.size «tab») «fullSize» packetWidth rw) («task₁»).cube.header.d ((«task₁»).cube.n+1)
      ((«task₁»).cube.h*(«task₁»).cube.b) («task₁»).cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.blocks («task₁»).cube.b («task₁»).cube.h («task₁»).cube.s)
    let «first» : ℕ := freeStartWith physical r 32 64 rw (lenPred+1)
    let «off» : ℕ := («early»).literal/4
    let «stripeWidth» : ℕ := GeometryAdviceRate.stripeWidth
      (GeometryOutput.packetCount reserve (Table.size «tab») «fullSize» packetWidth*rw) r
    let «stripe» := Allocation.stripe «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»
    let «place₀» := fun i : Fin (R+1) => ReaderPlacement.inArena «early»
      («places» i).valuation («places» i).entry («places» i).totals (Allocation.fields («pinned» i) «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»)
    let «slot₁» : ℕ := adviceOffsetWith physical r 32 64 rw (lenPred+1)
    let «args₁» := fun i : Fin (R+1) => («early»).unitAddresses «slot₁» (reader.packetAt («place₀» i))
    let «deployed» := reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
      copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget
    let «machine» := wiringWith physical P «deployed» indexWidth link (lenPred+1) ec machineFit
    let «clockFrame» := fun i : Fin (R+1) => («machine»).transferFrame i ((«args₁») i).header ((«args₁») i).dst
    let «pl» := privateLayout («early»).frame dest («task₁»).cube.cables cells «J₁» «desc» «dataGap»
    let «portB» := bases dest («task₁»).cube.cables cells «J₁»
    let «ctlB» : ℕ := controlsBase dest («task₁»).cube.cables cells «J₁» «live₁»
    let «loaded₁» : ℕ := schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
    let «birth₁» : ℕ := max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Packing.DeckGrid.Direction axes))))
    let «coefficient₁» : ℕ := (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
    let «scalar₁» : ℕ := max (15*«loaded₁») («H₁»).sites +
      max (max «birth₁» («coefficient₁»*(«loaded₁»+1))) (max 1 (15*«loaded₁»))+1
    ∀ {slope power coeff : ℕ}
    (_digitsChoice : digits=packetWidth)
    (_capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=paid))
    (_inputBounds : SignedPacketInputBounds schedule (d+1) T cells «live₁» «w» packetWidth slope power coeff gadgets «fmt» «publicDir» rfl number)
    (_numerals : FrozenPacketNumerals paid number gadgets hdr packetWidth «scalar₁» «loaded₁»)
    (_packetAddress : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth packetWidth<2^packetWidth)
    (_gateFit : (geometryTable «aug» «order₁» fit «fullEmit» x).size≤«gateCeiling»)
    (_geometryDest : Allocation.dest «fresh» reserve «gateCeiling» «fullSize» packetWidth=dest)
    (_headerWidth : wireLayout.header=JointHeader.PositiveFields.width reserve («task₁»).cube.n («task₁»).cube.header.d
      («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (fixed : Routing.Block (R+1))
    (regions : JointRoom «dir₁» «first» a (signedBootStripe «first») «stripe»)
    (copiesFit : reader.packetBitCount≤r)
    (_wfit : packetWidth≤rw)
    (_endFits : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth rw<2^rw)
    (memFit : («early»).next<2^rw)
    (hw : 0<rw)
    (threeTeams : 2<R+1)
    (hdrPos : 0<wireLayout.header)
    (cap : wireLayout.header≤r*link)
    (clock : ∀ u,packetUnitBudget ((«args₁») u).advice.count rw («clockFrame» u)
      ((«machine»).pinLayout u ((«args₁») u).ibase ((«args₁») u).hbase ((«args₁») u).starbase)≤basis.limit.val)
    (p : JointHeader.PositiveFields reserve («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (pin : Fin indexWidth → Bool)
    (ex : {z // PositiveExterior «machine» «args₁» pin rw z})
    (_common : ∀ b, JointHeader.observed wireLayout ex.val b=p.bits)
    (_encoded : «code₁»=p.profile)
    (bufferExtent : ℕ)
    (_budgetFits : exteriorBudget<2^rw)
    (_room₀ : («task₁»).cube.stop<2^rw)
    (_cellsFit : cells≤2^rw)
    (_span : («early»).next+7*(«dir₁»).candidates≤dest)
    (_rawRoom : («early»).next+7*(«dir₁»).candidates≤(«task₁»).cube.header.header)
    (_rs : r≤«tiles»)
    (posR : 0<r)
    (positiveTail : 0<((«actual»).program.length+«rTime»)/2)
    (_privateTail : «J₁»*«desc»≤(R+1)*r*(((«actual»).program.length+«rTime»)/2))
    (_localRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+(∑ j,if cells₁ («hosts₁» j)=c then «desc» else 0)≤(«task₁»).cube.cellStride)
    (_globalRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+«J₁»*«desc»≤bufferExtent)
    (_ctlBound : «ctlB»+8<2^rw)
    (_wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound («dir₁») («pl»).raw («portB»).livePairs bufferExtent)<2^rw)
    (_shortDescription : «desc»≤(«dir₁»).literal)
    (_teamCount : («task₁»).cube.teams=R+1)
    (guard : SelectedRawWriterRoom («task₁»).cube «dir₁» rw exteriorBudget («early»).next reserve («tab»).size «fullSize» packetWidth)
    (_sparse : ExternalSew.intercellWidth «finalN» cells₁≤2*(«dir₁»).teams*exteriorBudget)
    {α ξ : ℝ}
    (_route : RouteTableInputs («task₁»).cube «dir₁» α ξ (lenPred+1) rw («early»).frame link),
    let chosen := reader.deployedFrozenSites_boots physical P basis machineFit W position sites edges ports copies
      ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock
    let nodes := chosen.2.choose pin ex
    ∀ (u : Fin (R+1)) (g : Fin (nodes u).start.guessWidth → Bool),
      let pk := reader.packetAt («place₀» u)
      let node := nodes u
      let lib := install SparseExterior.driver (lenPred+1) node.start.routines
      let pub := («deployed»).publicWords u
      let bank := («deployed»).registers u
      let op := («early»).operands u «slot₁» pk
      let ad := («args₁») u
      let fs := («machine»).processorFields u pin ex.val ad.ibase ad.hbase ad.starbase
      let init := processorMemory fs rw
      let bc := («machine»).transferFrame u ad.header ad.dst
      let time := jointBudget pk.bits.length rw+bc.readTicks+2+((pinSetup.slots+17*op.layout.count+1)+
        GeometryAdviceRate.ticks («tab»).size reserve «fullSize» packetWidth rw)
      let rowBounds : («dir₁»).DestinationBounds := by
        refine ⟨positiveTail,hg,posR,le_rfl,?_⟩
        simpa only [«dir₁»,«rTime»,«g₁»,freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
          gridRoom «actual» (show 0<«tiles» from Fintype.card_pos)
      let rows := NativeDemands.rows «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
      let recv := NativeDemands.receiver «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap» rowBounds
      let sizes := fun i : Fin rows.length => rows[i.val].width
      let priv := NativeDemands.privatePair «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
      let live := NativeDemands.livePair «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
      let ar := («task₁»).cube
      let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) p.cube.1)
      let decl := Prod.mk axis (fun (e : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (p.cube.2 e j))
      let label := meanPackedLabel «finalN» cells₁ recv sizes (List.finRange cells) ar.n ar.header.d (Nat.zero_lt_of_lt guard.two)
      let mass := declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv sizes
      let group := fun j : Fin ar.header.d => TeamNative.owner R mass j.val
      let owner := fun c : ℕ => if h:c<cells then group (label ⟨c,h⟩ axis) else 0
      let supply := Sum.elim (fun z : SuppliedWord «finalN» cells₁ => z.1) (id : Fin cells → Fin cells)
      let supplyBits := Sum.elim (supplyWidth «finalN» cells₁) (fun _ : Fin cells => «dataGap»)
      let rowKey := numbered (reserveID (C:=cells) (suppliedID «finalN» cells₁ edge₁ port₁))
      let host := Sum.elim supply (cells₁ ∘ «hosts₁»)
      let fieldSize := Sum.elim supplyBits (fun _ : Fin («dir₁»).entries => «desc»)
      let ctl := controlsBase «origin» ar.cables ar.cells («dir₁»).entries ((«dir₁»).teams*(«dir₁»).sites)
      let previous := routingExtension ((«task₁»).extension raw u.val rw (signedBudgetWords rw exteriorBudget)) «dir₁» «origin» ar.cables ar.cells
      declarationInRange p.cube →
      broadcastAllowed R exteriorBudget ar.header.blocks ar.b ar.K ar.h label recv sizes p.cube →
      ∃ (ret : Returns (withStartup pinGeometry) pub lib bank init)
        (site : SignedPrep.CandidateSite (X:=exteriorBudget) ar «dir₁» priv live p.cube owner decl group
          («early»).frame («early»).next op.layout fs bc (Pins.extendGuess g) pub lib (node.pins g).val.2.1 (node.pins g).val.2.2
          host rowKey fieldSize «finalN» cells₁ recv sizes),
        site.OnReturn previous «fresh» («tab»).size «fullSize» packetWidth «off» «stripeWidth» ctl
          (List.ofFn p.profile) (DiagonalTallyRAM.broadcast rw p.rawCounts) 0 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins g).val.1) (traceCost ret.val.1) ∧
        traceCost ret.val.1≤time ∧ ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn g ∧
        BootResidence (F:=fs) «early» u «slot₁» pk bc ad.advice pub lib p.bits init bank g ret.val.2.2 ∧
        PublishedPin «task₁» «dir₁» «finalN» cells₁ edge₁ port₁ «hosts₁» livePorts «early» u «slot₁» pk «origin» «dataGap» bc p.bits fs
          pub lib g (node.pins g).val.2.1 (node.pins g).val.2.2 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins g).val.1) (traceCost ret.val.1) ∧
        Image F₂ ((«s₁»).rows.site ∘ «hosts₁») (port₁ ∘ livePorts ∘ finProdFinEquiv.symm)
          ((source₂).eval input₁) «origin» (readings ret.val.2.2) ∧
        (∀ j : Fin 37, readings ret.val.2.2 (ctl+j.val)=(«task₁»).controls j.val) ∧
        ∀ i : Fin «fullSize», readings ret.val.2.2 («origin»+i.val)=emittedWords «aug» «order₁» fit «fullEmit» x «code₁» i := by
  intro «G₀» «tiles» «w» «V» «extent» «header» «key» «fmt» «source» «seed₀» «compiled» «steps» «epochFormat» «aug» «base»
    «actual» «rTime» «s₁» «N₀» «code₁» «g₁» «p₁» «h₁» «finalN» «scp» «desc» «H₁» «J₁» «live₁» «dir₁» «publicDir»
    «boxes₁» «task₁» «ctrl₁» «dataArena» «dataStride» «dataGap» «hosts₁» «final₁» «priv₁» «reports₁» «tpl₁»
    «packetSize» «fullSize» «fullEmit» «gateCeiling» «order₁» «tab» «early» «gap» «fresh» «origin» «routed» «places»
    «pinned» «first» «off» «stripeWidth» «stripe» «place₀» «slot₁» «args₁» «deployed» «machine» «clockFrame» «pl»
    «portB» «ctlB» «loaded₁» «birth₁» «coefficient₁» «scalar₁» slope power coeff digitsChoice capChoice inputBounds
    numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit wfit endFits memFit hw threeTeams
    hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit span rawRoom rs posR positiveTail
    privateTail localRoom globalRoom ctlBound wordRoom shortDescription teamCount guard sparse α ξ route
    chosen nodes u g pk node lib pub bank op ad fs init bc time rowBounds rows recv sizes priv live ar
    axis decl label mass group owner supply supplyBits rowKey host fieldSize ctl previous valid allowed
  let publishedAtPin := reader.deployed_frozen_prefix_publication (physical:=physical) (P:=P) (basis:=basis) (machineFit:=machineFit) (W:=W) (position:=position)
    (sites:=sites) (edges:=edges) (ports:=ports) (plan:=plan) (wireLayout:=wireLayout) (x:=x) (seedTable:=seedTable)
    (wr:=wr) (hm:=hm) (seeds:=seeds) (number:=number) (widths:=widths) (ord:=ord) (fit:=fit) (count:=count)
    (cellNumber:=cellNumber) (vf:=vf) (cf:=cf) (hg:=hg) (short:=short) (pw:=pw) (extend:=extend) (room:=room)
    (hook:=hook) (histQ:=histQ) (hardwareTemplate:=hardwareTemplate) (sitePos:=sitePos) (cellPos:=cellPos)
    (ownerFits:=ownerFits) (gadgets:=gadgets) (digits:=digits) (ctrlFit:=ctrlFit) (hs:=hs) (hf:=hf) (keyFits:=keyFits)
    (sitesFit:=sitesFit) (keysFit:=keysFit) (sw:=sw) (pad:=pad) (dest:=dest) (hdr:=hdr) (bankLayout:=bankLayout)
    (bundleBits:=bundleBits) (shapes:=shapes) (U:=U) (deg:=deg) (exteriorBudget:=exteriorBudget)
    digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit wfit
    endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit span rawRoom
    rs posR positiveTail privateTail localRoom globalRoom ctlBound wordRoom
  obtain ⟨ret,paths,spelled,published,image,controls⟩ := publishedAtPin u g
  have headerLength := (congrArg List.length p.bits_eq_emitted).symm.trans (p.bits_length.trans headerWidth.symm)
  have topology := (plan.frozen_signed_packet_geometry «G₀» order position W signedTag sites edges ports
    seedTable x wr hm seeds number widths ord fit «actual» count cellNumber vf cf hg short pw extend room hook histQ).2.1
  have grid := (plan.frozen_leaf_installed «G₀» order position W signedTag sites edges ports seedTable x).trans
    (SewnTape.native_grid_installed order position physical P basis machineFit)
  have sizeFit := (plan.frozen_packet_operands «G₀» order position W signedTag sites edges ports seedTable x wr hm seeds number widths ord fit
    «actual» count cellNumber vf cf hg short pw extend room hook histQ «dir₁» sitePos cellPos
    «dataArena» «dataStride» «dataGap» «desc» gadgets digits hs hf dest hdr
    digitsChoice capChoice rfl inputBounds numerals grid «fresh» «gateCeiling» bundleBits geometryDest packetAddress).1
  have limits := guard.located_writer_fields (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth) bundleBits rfl shortDescription
  have slotFits : «slot₁»<(«early»).literal := by dsimp [«slot₁»,«early»,ChosenReader.startupArenaWith,programArena,adviceOffsetWith,entryLiteral]; omega
  have fits := («early»).fits u «slot₁» pk threeTeams posR ((Nat.zero_le _).trans_lt slotFits)
    (Nat.pos_of_mul_pos_left (hdrPos.trans_le cap)) hdrPos (Nat.mul_comm r link ▸ cap) slotFits
    (reader.packetAt_length _).le copiesFit memFit
  have heads := published_return_at_header p.bits_eq_emitted paths published
  obtain ⟨site,onReturn,cost,_,readback⟩ := reader.deployedFrozenSites_raw_candidate physical P basis machineFit W position
    sites edges ports copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget (List.ofFn p.profile)
    (DiagonalTallyRAM.broadcast rw p.rawCounts) 0 p.cube «finalN» cells₁ (fun v => (rawState v).program.size) («s₁»).rows.site edge₁ port₁ F₂
    «hosts₁» livePorts (fun _ => rfl) rowBounds u node g topology (fun _ => rfl) sizeFit ownerFits wfit cellPos privateTail
    time (emittedWords «aug» «order₁» fit «fullEmit» x «code₁») ret heads.1 spelled heads.2
    image controls (List.length_ofFn ..) headerLength fits.1 (Nat.le_trans (Nat.add_le_add_left (by decide : 28≤37) _) limits.1) limits.2
    teamCount posR (chosen.1 u).1.physical guard sparse route valid allowed
  exact ⟨ret,site,onReturn,cost,spelled,paths.memory ret g spelled,published,image,controls,readback⟩

include pw room hook seeds cellPos in
set_option maxHeartbeats 51200000 in
/-- Any actual returning joint tuple at the selected profile passes both raw
broadcast tests. Its own pin digits select the earlier frozen geometry, whose
published routing rows are available before the declaration is validated. -/
theorem ChosenReader.deployed_frozen_checked_header :
    let «G₀» := tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw)
      (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
    let «tiles» : ℕ := GridHosts.tileCount axes d
    let «w» : ℕ := 60*logWidth r (lenPred+1)
    let «V» : ℕ := CoverScale.sites (Cube D) (d+1)
    let «extent» : ℕ := copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
    let «header» := WorkWords.grouped «V» «extent»
    let «key» := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
    let «fmt» := Boundary.seedFormat «G₀» order position copies
    let «source» := plan.frozenStart «G₀» order position σ
    let «seed₀» := plan.frozenLeaf «G₀» order position W signedTag sites edges ports seedTable x
    let «compiled» := plan.compiled
    let «steps» := («compiled»).tapeSteps «fmt» «header» «key» wr hm
    let «epochFormat» := ProgramSchemas.epoch schedule (d+1) «w» «fmt» T
    let «aug» := compile «steps» T le_rfl (repeatLeaf (fan schedule) «source» T)
    let «base» := (plan.execute «G₀» order position σ).choose
    let «actual» := wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
    let «rTime» : ℕ := TeamContraction.cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
      (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
    let «s₁» := ((packHistory «seed₀» («compiled»).machine.epoch T).term histQ).val
    let «N₀» := (flattenPack T («s₁»).pack).layout
    let «code₁» := ((«compiled»).machine.nativeCode «seed₀» «base» x rfl widths ord fit histQ).val
    let «g₁» : ℕ := inputBlockWidth r (lenPred+1) axes d
    let «p₁» := (⟨R,r,(«actual»).program.length+«rTime»,link,«g₁»,«tiles»⟩ : FieldExport.Params)
    let «hp₁» := (⟨hg,short,gridRoom «actual» Fintype.card_pos⟩ : («p₁»).Valid)
    let «h₁» := attachedHosts «actual» Fintype.card_pos count «N₀»
    let «edge₁» := mergedEdges «p₁» «hp₁» («s₁»).rows.edge
    let «port₁» := (finProdFinEquiv : FreeBlock R «tiles» ≃ Fin ((R+1)*«tiles»)).toEmbedding
    let «finalN» := finalLayout «p₁» «h₁»
    let «scp» := («epochFormat»).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*«tiles») «w»)
    let «desc» : ℕ := seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
      (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
    let «H₁» := boundaryShape schedule (d+1) T
    let «J₁» : ℕ := (fan schedule)^T*«tiles»
    let «live₁» : ℕ := (R+1)*«tiles»
    let «dir₁» := freeDirectory R r ((«actual»).program.length+«rTime») link «tiles» «g₁» «J₁» «desc»
    let «publicDir» := {(«dir₁») with sites := «tiles», entries := «J₁»}
    let «boxes₁» := scheduledBoxes «publicDir» rfl number sitePos
    let «task₁» := hardwareTemplate.withNetwork cells ((«H₁»).edges+(«p₁»).slots)
    let «ctrl₁» := fun i : Fin 37 => (⟨(«task₁»).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
    let «dataArena» : ℕ := («task₁»).cube.cellBank
    let «dataStride» : ℕ := («task₁»).cube.cellStride
    let «dataGap» : ℕ := («task₁»).p.privateGap
    let «hosts₁» := originalDescriptionRows plan.compiled.machine «seed₀» histQ «dir₁» rfl order
    let «livePorts» := Function.Embedding.refl (Fin (R+1) × Fin «tiles»)
    let «final₁» := FinalTies.tieSchema ((«H₁»).edges+(«p₁»).slots) «live₁» packetWidth
    let «priv₁» := FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «reports₁» := FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «tpl₁» := template «scp» «final₁» «boxes₁» hs hf «priv₁» «reports₁»
    let «packetSize» : ℕ := signedGridOutputCount ((«H₁»).edges+4*(R+1)*«tiles») cells «J₁» «live₁»
      37 (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth)
    let «fullSize» : ℕ := «packetSize»+(2^bundleBits+2^bundleBits)
    let «fullEmit» := frozenPacketWithBundles (reserve := reserve) schedule «G₀» order position σ «actual»
      count cellNumber vf cf hg short extend («dir₁») number sitePos ownerFits «dataArena» «dataStride» «dataGap» «desc» gadgets digits «ctrl₁» hs hf
      keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes
    let «gateCeiling» : ℕ := geometryGateCeiling U deg r (lenPred+1)
    let «order₁» := broadcastOrder (fan schedule) widths ord T
    let «tab» := reservedGeometryTable «aug» «order₁» fit «fullEmit» x «gateCeiling»
    let «early» := reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
    let «gap» : ℕ := 7*(«dir₁»).candidates
    let «fresh» : ℕ := («early»).next+«gap»
    let «origin» : ℕ := Allocation.dest «fresh» reserve (Table.size «tab») «fullSize» packetWidth
    let «routed» := routingExtension (signedBudgetWords rw exteriorBudget)
      «dir₁» «origin» («task₁»).cube.cables («task₁»).cube.cells
    let «places» := fun i : Fin (R+1) => reader.frozenTaskPlacement «task₁» «early» i «routed»
    let «pinned» := fun i : Fin (R+1) => CubeHeaderInstall.pinFields («places» i).extension
      (Allocation.stop «fresh» reserve (Table.size «tab») «fullSize» packetWidth rw) («task₁»).cube.header.d ((«task₁»).cube.n+1)
      ((«task₁»).cube.h*(«task₁»).cube.b) («task₁»).cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.blocks («task₁»).cube.b («task₁»).cube.h («task₁»).cube.s)
    let «first» : ℕ := freeStartWith physical r 32 64 rw (lenPred+1)
    let «off» : ℕ := («early»).literal/4
    let «stripeWidth» : ℕ := GeometryAdviceRate.stripeWidth
      (GeometryOutput.packetCount reserve (Table.size «tab») «fullSize» packetWidth*rw) r
    let «stripe» := Allocation.stripe «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»
    let «place₀» := fun i : Fin (R+1) => ReaderPlacement.inArena «early»
      («places» i).valuation («places» i).entry («places» i).totals (Allocation.fields («pinned» i) «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»)
    let «slot₁» : ℕ := adviceOffsetWith physical r 32 64 rw (lenPred+1)
    let «args₁» := fun i : Fin (R+1) => («early»).unitAddresses «slot₁» (reader.packetAt («place₀» i))
    let «deployed» := reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
      copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget
    let «machine» := wiringWith physical P «deployed» indexWidth link (lenPred+1) ec machineFit
    let «clockFrame» := fun i : Fin (R+1) => («machine»).transferFrame i ((«args₁») i).header ((«args₁») i).dst
    let «pl» := privateLayout («early»).frame dest («task₁»).cube.cables cells «J₁» «desc» «dataGap»
    let «portB» := bases dest («task₁»).cube.cables cells «J₁»
    let «ctlB» : ℕ := controlsBase dest («task₁»).cube.cables cells «J₁» «live₁»
    let «loaded₁» : ℕ := schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
    let «birth₁» : ℕ := max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
    let «coefficient₁» : ℕ := (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
    let «scalar₁» : ℕ := max (15*«loaded₁») («H₁»).sites +
      max (max «birth₁» («coefficient₁»*(«loaded₁»+1))) (max 1 (15*«loaded₁»))+1
    ∀ {slope power coeff : ℕ}
    (_digitsChoice : digits=packetWidth)
    (_capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=paid))
    (_inputBounds : SignedPacketInputBounds schedule (d+1) T cells «live₁» «w» packetWidth slope power coeff gadgets «fmt» «publicDir» rfl number)
    (_numerals : FrozenPacketNumerals paid number gadgets hdr packetWidth «scalar₁» «loaded₁»)
    (_packetAddress : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth packetWidth<2^packetWidth)
    (_gateFit : (geometryTable «aug» «order₁» fit «fullEmit» x).size≤«gateCeiling»)
    (_geometryDest : Allocation.dest «fresh» reserve «gateCeiling» «fullSize» packetWidth=dest)
    (_headerWidth : wireLayout.header=JointHeader.PositiveFields.width reserve («task₁»).cube.n («task₁»).cube.header.d
      («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (fixed : Routing.Block (R+1))
    (regions : JointRoom «dir₁» «first» a (signedBootStripe «first») «stripe»)
    (copiesFit : reader.packetBitCount≤r)
    (_wfit : packetWidth≤rw)
    (_endFits : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth rw<2^rw)
    (memFit : («early»).next<2^rw)
    (hw : 0<rw)
    (threeTeams : 2<R+1)
    (hdrPos : 0<wireLayout.header)
    (cap : wireLayout.header≤r*link)
    (clock : ∀ u,packetUnitBudget ((«args₁») u).advice.count rw («clockFrame» u)
      ((«machine»).pinLayout u ((«args₁») u).ibase ((«args₁») u).hbase ((«args₁») u).starbase)≤basis.limit.val)
    (p : JointHeader.PositiveFields reserve («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (pin : Fin indexWidth → Bool)
    (ex : {z // PositiveExterior «machine» «args₁» pin rw z})
    (_common : ∀ b, JointHeader.observed wireLayout ex.val b=p.bits)
    (_encoded : «code₁»=p.profile)
    (bufferExtent : ℕ)
    (_budgetFits : exteriorBudget<2^rw)
    (_room₀ : («task₁»).cube.stop<2^rw)
    (_cellsFit : cells≤2^rw)
    (_span : («early»).next+7*(«dir₁»).candidates≤dest)
    (_rawRoom : («early»).next+7*(«dir₁»).candidates≤(«task₁»).cube.header.header)
    (_rs : r≤«tiles»)
    (posR : 0<r)
    (positiveTail : 0<((«actual»).program.length+«rTime»)/2)
    (_privateTail : «J₁»*«desc»≤(R+1)*r*(((«actual»).program.length+«rTime»)/2))
    (_localRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+(∑ j,if cells₁ («hosts₁» j)=c then «desc» else 0)≤(«task₁»).cube.cellStride)
    (_globalRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+«J₁»*«desc»≤bufferExtent)
    (_ctlBound : «ctlB»+8<2^rw)
    (_wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound («dir₁») («pl»).raw («portB»).livePairs bufferExtent)<2^rw)
    (_shortDescription : «desc»≤(«dir₁»).literal)
    (_teamCount : («task₁»).cube.teams=R+1)
    (guard : SelectedRawWriterRoom («task₁»).cube «dir₁» rw exteriorBudget («early»).next reserve («tab»).size «fullSize» packetWidth)
    (_sparse : ExternalSew.intercellWidth «finalN» cells₁≤2*(«dir₁»).teams*exteriorBudget)
    {α ξ : ℝ}
    (_route : RouteTableInputs («task₁»).cube «dir₁» α ξ (lenPred+1) rw («early»).frame link),
    let chosen := reader.deployedFrozenSites_boots physical P basis machineFit W position sites edges ports copies
      ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock
    let nodes := chosen.2.choose pin ex
    PinStart.JointPrefix («task₁»).id (fun u => (nodes u).start) →
    let rowBounds : («dir₁»).DestinationBounds := (by
      refine ⟨positiveTail,hg,posR,le_rfl,?_⟩
      simpa only [«dir₁»,«rTime»,«g₁»,freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
        gridRoom «actual» (show 0<«tiles» from Fintype.card_pos))
    let rows := NativeDemands.rows «finalN» cells₁ «edge₁» «port₁» «dir₁» «hosts₁» «livePorts» «dataGap»
    let recv := NativeDemands.receiver «finalN» cells₁ «edge₁» «port₁» «dir₁» «hosts₁» «livePorts» «dataGap» rowBounds
    let sizes := fun i : Fin rows.length => rows[i.val].width
    let ar := («task₁»).cube
    let label := meanPackedLabel «finalN» cells₁ recv sizes (List.finRange cells) ar.n ar.header.d (Nat.zero_lt_of_lt guard.two)
    declarationInRange p.cube ∧ broadcastAllowed R exteriorBudget ar.header.blocks ar.b ar.K ar.h label recv sizes p.cube := by
  intro «G₀» «tiles» «w» «V» «extent» «header» «key» «fmt» «source» «seed₀» «compiled» «steps» «epochFormat» «aug» «base»
    «actual» «rTime» «s₁» «N₀» «code₁» «g₁» «p₁» «hp₁» «h₁» «edge₁» «port₁» «finalN» «scp» «desc» «H₁» «J₁» «live₁»
    «dir₁» «publicDir» «boxes₁» «task₁» «ctrl₁» «dataArena» «dataStride» «dataGap» «hosts₁» «livePorts» «final₁»
    «priv₁» «reports₁» «tpl₁» «packetSize» «fullSize» «fullEmit» «gateCeiling» «order₁» «tab» «early» «gap» «fresh»
    «origin» «routed» «places» «pinned» «first» «off» «stripeWidth» «stripe» «place₀» «slot₁» «args₁» «deployed»
    «machine» «clockFrame» «pl» «portB» «ctlB» «loaded₁» «birth₁» «coefficient₁» «scalar₁» slope power coeff
    digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit
    wfit endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit
    span rawRoom rs posR positiveTail privateTail localRoom globalRoom ctlBound wordRoom shortDescription teamCount
    guard sparse α ξ route chosen nodes tuple rowBounds rows recv sizes ar label
  let u : Fin (R+1) := 0
  let node := nodes u
  let g := (tuple u).1
  let pk := reader.packetAt («place₀» u)
  let pinReturns := reader.deployed_frozen_prefix_publication (physical:=physical) (P:=P) (basis:=basis) (machineFit:=machineFit) (W:=W) (position:=position)
    (sites:=sites) (edges:=edges) (ports:=ports) (plan:=plan) (wireLayout:=wireLayout) (x:=x) (seedTable:=seedTable)
    (wr:=wr) (hm:=hm) (seeds:=seeds) (number:=number) (widths:=widths) (ord:=ord) (fit:=fit) (count:=count)
    (cellNumber:=cellNumber) (vf:=vf) (cf:=cf) (hg:=hg) (short:=short) (pw:=pw) (extend:=extend) (room:=room)
    (hook:=hook) (histQ:=histQ) (hardwareTemplate:=hardwareTemplate) (sitePos:=sitePos) (cellPos:=cellPos)
    (ownerFits:=ownerFits) (gadgets:=gadgets) (digits:=digits) (ctrlFit:=ctrlFit) (hs:=hs) (hf:=hf) (keyFits:=keyFits)
    (sitesFit:=sitesFit) (keysFit:=keysFit) (sw:=sw) (pad:=pad) (dest:=dest) (hdr:=hdr) (bankLayout:=bankLayout)
    (bundleBits:=bundleBits) (shapes:=shapes) (U:=U) (deg:=deg) (exteriorBudget:=exteriorBudget)
    digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit wfit
    endFits memFit hw threeTeams hdrPos cap clock p pin ex common encoded bufferExtent budgetFits room₀ cellsFit span rawRoom
    rs posR positiveTail privateTail localRoom globalRoom ctlBound wordRoom
  obtain ⟨ret,paths,spelled,published,image,controls⟩ := pinReturns u g
  have headerLength := (congrArg List.length p.bits_eq_emitted).symm.trans (p.bits_length.trans headerWidth.symm)
  have topology := (plan.frozen_signed_packet_geometry «G₀» order position W signedTag sites edges ports
    seedTable x wr hm seeds number widths ord fit «actual» count cellNumber vf cf hg short pw extend room hook histQ).2.1
  have grid := (plan.frozen_leaf_installed «G₀» order position W signedTag sites edges ports seedTable x).trans
    (SewnTape.native_grid_installed order position physical P basis machineFit)
  have sizeFit := (plan.frozen_packet_operands «G₀» order position W signedTag sites edges ports seedTable x wr hm seeds number widths ord fit
    «actual» count cellNumber vf cf hg short pw extend room hook histQ «dir₁» sitePos cellPos «dataArena» «dataStride» «dataGap» «desc» gadgets digits hs hf dest hdr
    digitsChoice capChoice rfl inputBounds numerals grid «fresh» «gateCeiling» bundleBits geometryDest packetAddress).1
  have limits := guard.located_writer_fields (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth) bundleBits rfl shortDescription
  have slotFits : «slot₁»<(«early»).literal := by dsimp [«slot₁»,«early»,ChosenReader.startupArenaWith,programArena,adviceOffsetWith,entryLiteral]; omega
  have fits := («early»).fits u «slot₁» pk threeTeams posR ((Nat.zero_le _).trans_lt slotFits)
    (Nat.pos_of_mul_pos_left (hdrPos.trans_le cap)) hdrPos (Nat.mul_comm r link ▸ cap) slotFits
    (reader.packetAt_length _).le copiesFit memFit
  have heads := published_return_at_header p.bits_eq_emitted paths published
  have publishedHeader := heads.2
  have sameHeader := heads.1.memory ret g spelled
  obtain ⟨dictionary,spells⟩ := paths.outputs trivial
  have checked := reader.deployedFrozenSites_pin_writer physical P basis machineFit W position
    sites edges ports copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget (List.ofFn p.profile)
    (DiagonalTallyRAM.broadcast rw p.rawCounts) 0 p.cube «finalN» cells₁ (fun v => (rawState v).program.size) («s₁»).rows.site «edge₁» «port₁» F₂
    «hosts₁» «livePorts» (fun _ => rfl) rowBounds («task₁»).id nodes tuple u topology (fun _ => rfl) sizeFit ownerFits wfit cellPos privateTail
    dictionary (fun z => (spells z).1) ret spelled sameHeader
    publishedHeader image controls (List.length_ofFn ..) headerLength fits.1
    (Nat.le_trans (Nat.add_le_add_left (by decide : 28≤37) _) limits.1) limits.2 teamCount posR guard sparse route
  exact ⟨checked.2.1,checked.2.2.1⟩



include pw room hook seeds cellPos in
set_option maxHeartbeats 32000000 in
/-- For this actual frozen history and checked declaration, construct its real
wire and source frame on every physical exterior and every original pin digit.
All geometry, terminal banks, rows, timing and pre-call source words of the
chosen team are retained on the same returned RAM. -/
theorem ChosenReader.deployed_frozen_candidate_frame :
    let «G₀» := tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) («w»:=rw)
      (e:=ec) (width:=rw+1) (k:=lenPred) (a:=tail) physical machineFit indexWidth
    let «tiles» : ℕ := GridHosts.tileCount axes d
    let «w» : ℕ := 60*logWidth r (lenPred+1)
    let «V» : ℕ := CoverScale.sites (Cube D) (d+1)
    let «extent» : ℕ := copies*GridHosts.inputBlockWidth r (lenPred+1) axes d
    let «header» := WorkWords.grouped «V» «extent»
    let «key» := Equiv.toEmbedding (finCongr (seedPortCount (D:=D) d))
    let «fmt» := Boundary.seedFormat «G₀» order position copies
    let «source» := plan.frozenStart «G₀» order position σ
    let «seed₀» := plan.frozenLeaf «G₀» order position W signedTag sites edges ports seedTable x
    let «compiled» := plan.compiled
    let «steps» := («compiled»).tapeSteps «fmt» «header» «key» wr hm
    let «epochFormat» := ProgramSchemas.epoch schedule (d+1) «w» «fmt» T
    let «aug» := compile «steps» T le_rfl (repeatLeaf (fan schedule) «source» T)
    let «base» := (plan.execute «G₀» order position σ).choose
    let «actual» := wiringWith physical P basis indexWidth link (lenPred+1) ec machineFit
    let «rTime» : ℕ := TeamContraction.cutWidth (lenPred+1)+(setupWidth (rw+1) (lenPred+1)+
      (prefixCapacity r 32 64 rw (lenPred+1)+1+a))
    let «s₁» := ((packHistory «seed₀» («compiled»).machine.epoch T).term histQ).val
    let «N₀» := (flattenPack T («s₁»).pack).layout
    let «code₁» := ((«compiled»).machine.nativeCode «seed₀» «base» x rfl widths ord fit histQ).val
    let «g₁» : ℕ := inputBlockWidth r (lenPred+1) axes d
    let «p₁» := (⟨R,r,(«actual»).program.length+«rTime»,link,«g₁»,«tiles»⟩ : FieldExport.Params)
    let «h₁» := attachedHosts «actual» Fintype.card_pos count «N₀»
    let «finalN» := finalLayout «p₁» «h₁»
    let «scp» := («epochFormat»).schema.append
      (Sewn.schema (2*(boundaryShape schedule (d+1) T).edges+6*(R+1)*«tiles») «w»)
    let «desc» : ℕ := seedDescriptionWidth (lenPred+1) r axes d (headerFactor*logWidth r (lenPred+1))
      (BottomGridBank.bodyBudget (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
    let «H₁» := boundaryShape schedule (d+1) T
    let «J₁» : ℕ := (fan schedule)^T*«tiles»
    let «live₁» : ℕ := (R+1)*«tiles»
    let «dir₁» := freeDirectory R r ((«actual»).program.length+«rTime») link «tiles» «g₁» «J₁» «desc»
    let «publicDir» := {(«dir₁») with sites := «tiles», entries := «J₁»}
    let «boxes₁» := scheduledBoxes «publicDir» rfl number sitePos
    let «task₁» := hardwareTemplate.withNetwork cells ((«H₁»).edges+(«p₁»).slots)
    let «ctrl₁» := fun i : Fin 37 => (⟨(«task₁»).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
    let «dataArena» : ℕ := («task₁»).cube.cellBank
    let «dataStride» : ℕ := («task₁»).cube.cellStride
    let «dataGap» : ℕ := («task₁»).p.privateGap
    let «hosts₁» := originalDescriptionRows plan.compiled.machine «seed₀» histQ «dir₁» rfl order
    let «final₁» := FinalTies.tieSchema ((«H₁»).edges+(«p₁»).slots) «live₁» packetWidth
    let «priv₁» := FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «reports₁» := FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin «J₁»)
    let «tpl₁» := template «scp» «final₁» «boxes₁» hs hf «priv₁» «reports₁»
    let «packetSize» : ℕ := signedGridOutputCount ((«H₁»).edges+4*(R+1)*«tiles») cells «J₁» «live₁»
      37 (Total («tpl₁»).publicDepth («tpl₁»).chunkDepth)
    let «fullSize» : ℕ := «packetSize»+(2^bundleBits+2^bundleBits)
    let «fullEmit» := frozenPacketWithBundles (reserve := reserve) schedule «G₀» order position σ «actual»
      count cellNumber vf cf hg short extend («dir₁») number sitePos ownerFits «dataArena» «dataStride» «dataGap» «desc» gadgets digits «ctrl₁» hs hf
      keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes
    let «gateCeiling» : ℕ := geometryGateCeiling U deg r (lenPred+1)
    let «order₁» := broadcastOrder (fan schedule) widths ord T
    let «tab» := reservedGeometryTable «aug» «order₁» fit «fullEmit» x «gateCeiling»
    let «early» := reader.startupArenaWith (n:=lenPred+1) (reg:=64) physical a link wireLayout.header
    let «gap» : ℕ := 7*(«dir₁»).candidates
    let «fresh» : ℕ := («early»).next+«gap»
    let «origin» : ℕ := Allocation.dest «fresh» reserve (Table.size «tab») «fullSize» packetWidth
    let «routed» := routingExtension (signedBudgetWords rw exteriorBudget)
      «dir₁» «origin» («task₁»).cube.cables («task₁»).cube.cells
    let «places» := fun i : Fin (R+1) => reader.frozenTaskPlacement «task₁» «early» i «routed»
    let «pinned» := fun i : Fin (R+1) => CubeHeaderInstall.pinFields («places» i).extension
      (Allocation.stop «fresh» reserve (Table.size «tab») «fullSize» packetWidth rw) («task₁»).cube.header.d ((«task₁»).cube.n+1)
      ((«task₁»).cube.h*(«task₁»).cube.b) («task₁»).cube.header.blocks reserve
      (BorderVNP.Cube.Physical.declarationCap («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.blocks («task₁»).cube.b («task₁»).cube.h («task₁»).cube.s)
    let «first» : ℕ := freeStartWith physical r 32 64 rw (lenPred+1)
    let «off» : ℕ := («early»).literal/4
    let «stripeWidth» : ℕ := GeometryAdviceRate.stripeWidth
      (GeometryOutput.packetCount reserve (Table.size «tab») «fullSize» packetWidth*rw) r
    let «stripe» := Allocation.stripe «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»
    let «place₀» := fun i : Fin (R+1) => ReaderPlacement.inArena «early»
      («places» i).valuation («places» i).entry («places» i).totals (Allocation.fields («pinned» i) «fresh» reserve (Table.size «tab») «fullSize» packetWidth «off» «stripeWidth»)
    let «slot₁» : ℕ := adviceOffsetWith physical r 32 64 rw (lenPred+1)
    let «args₁» := fun i : Fin (R+1) => («early»).unitAddresses «slot₁» (reader.packetAt («place₀» i))
    let «deployed» := reader.deployedFrozenSites physical P basis machineFit W position sites edges ports
      copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget
    let «machine» := wiringWith physical P «deployed» indexWidth link (lenPred+1) ec machineFit
    let «clockFrame» := fun i : Fin (R+1) => («machine»).transferFrame i ((«args₁») i).header ((«args₁») i).dst
    let «pl» := privateLayout («early»).frame dest («task₁»).cube.cables cells «J₁» «desc» «dataGap»
    let «portB» := bases dest («task₁»).cube.cables cells «J₁»
    let «ctlB» : ℕ := controlsBase dest («task₁»).cube.cables cells «J₁» «live₁»
    let «loaded₁» : ℕ := schedule.publicProgramFactor^T*initialMass (D:=D) (lenPred+1) r d copies headerFactor
    let «birth₁» : ℕ := max 2 (max copies (seedBoxCapacity (lenPred+1) r axes d (Fintype.card (Direction axes))))
    let «coefficient₁» : ℕ := (birthWordCoefficient paid+8)*(BankCharges.bound paid+1)*(schedule.populationFactor+2)
    let «scalar₁» : ℕ := max (15*«loaded₁») («H₁»).sites +
      max (max «birth₁» («coefficient₁»*(«loaded₁»+1))) (max 1 (15*«loaded₁»))+1
    ∀ {slope power coeff : ℕ}
    (_digitsChoice : digits=packetWidth)
    (_capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=paid))
    (_inputBounds : SignedPacketInputBounds schedule (d+1) T cells «live₁» «w» packetWidth slope power coeff gadgets «fmt» «publicDir» rfl number)
    (_numerals : FrozenPacketNumerals paid number gadgets hdr packetWidth «scalar₁» «loaded₁»)
    (_packetAddress : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth packetWidth<2^packetWidth)
    (_gateFit : (geometryTable «aug» «order₁» fit «fullEmit» x).size≤«gateCeiling»)
    (_geometryDest : Allocation.dest «fresh» reserve «gateCeiling» «fullSize» packetWidth=dest)
    (headerWidth : wireLayout.header=JointHeader.PositiveFields.width reserve («task₁»).cube.n («task₁»).cube.header.d
      («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (fixed : Routing.Block (R+1))
    (regions : JointRoom «dir₁» «first» a (signedBootStripe «first») «stripe»)
    (copiesFit : reader.packetBitCount≤r)
    (_wfit : packetWidth≤rw)
    (_endFits : Allocation.stop «fresh» reserve «gateCeiling» «fullSize» packetWidth rw<2^rw)
    (memFit : («early»).next<2^rw)
    (hw : 0<rw)
    (threeTeams : 2<R+1)
    (hdrPos : 0<wireLayout.header)
    (cap : wireLayout.header≤r*link)
    (clock : ∀ u,packetUnitBudget ((«args₁») u).advice.count rw («clockFrame» u)
      ((«machine»).pinLayout u ((«args₁») u).ibase ((«args₁») u).hbase ((«args₁») u).starbase)≤basis.limit.val)
    (p : JointHeader.PositiveFields reserve («task₁»).cube.n («task₁»).cube.header.d («task₁»).cube.header.cap (R+1) («task₁»).dim rw)
    (pin : Fin indexWidth → Bool)
    (rawPin : Fin indexWidth → Bool)
    (_encoded : «code₁»=p.profile)
    (bufferExtent : ℕ)
    (_budgetFits : exteriorBudget<2^rw)
    (_room₀ : («task₁»).cube.stop<2^rw)
    (_cellsFit : cells≤2^rw)
    (_span : («early»).next+7*(«dir₁»).candidates≤dest)
    (_rawRoom : («early»).next+7*(«dir₁»).candidates≤(«task₁»).cube.header.header)
    (_rs : r≤«tiles»)
    (posR : 0<r)
    (positiveTail : 0<((«actual»).program.length+«rTime»)/2)
    (_privateTail : «J₁»*«desc»≤(R+1)*r*(((«actual»).program.length+«rTime»)/2))
    (_localRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+(∑ j,if cells₁ («hosts₁» j)=c then «desc» else 0)≤(«task₁»).cube.cellStride)
    (_globalRoom : ∀ c,suppliedSize «finalN» cells₁ c+«dataGap»+«J₁»*«desc»≤bufferExtent)
    (_ctlBound : «ctlB»+8<2^rw)
    (_wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound («dir₁») («pl»).raw («portB»).livePairs bufferExtent)<2^rw)
    (_shortDescription : «desc»≤(«dir₁»).literal)
    (_teamCount : («task₁»).cube.teams=R+1)
    (guard : SelectedRawWriterRoom («task₁»).cube «dir₁» rw exteriorBudget («early»).next reserve («tab»).size «fullSize» packetWidth)
    (_sparse : ExternalSew.intercellWidth «finalN» cells₁≤2*(«dir₁»).teams*exteriorBudget)
    {α ξ : ℝ}
    (_route : RouteTableInputs («task₁»).cube «dir₁» α ξ (lenPred+1) rw («early»).frame link)
    (_budgetEq : exteriorBudget=TeamScales.exterior ξ r (lenPred+1))
    (_literalBound : («dir₁»).literal≤TeamScales.literal α (lenPred+1))
    (_headerBound : (wireLayout.header:ℝ) ≤ r*((lenPred+1:ℕ):ℝ)^(24/25:ℝ)),
    let chosen := reader.deployedFrozenSites_boots physical P basis machineFit W position sites edges ports copies
      ((fan schedule)^T) headerFactor wireLayout «tab» «task₁» exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock
    let certified := fun z : HeaderExterior wireLayout p.bits => reader.deployed_header_receipts
      physical P basis machineFit W position sites edges ports copies ((fan schedule)^T) headerFactor wireLayout «tab» «task₁»
      exteriorBudget fixed regions copiesFit memFit hw threeTeams hdrPos cap clock headerWidth pin p z
    let exterior := fun z : HeaderExterior wireLayout p.bits =>
      (⟨z.val,(certified z).choose⟩ : {z // PositiveExterior «machine» «args₁» pin rw z})
    let nodes := fun z => chosen.2.choose pin (exterior z)
    let ib := fun u : Fin (R+1) => ((«args₁») u).ibase
    let hb := fun u : Fin (R+1) => ((«args₁») u).hbase
    let sb := fun u : Fin (R+1) => ((«args₁») u).starbase
    let dst := fun u : Fin (R+1) => ((«args₁») u).dst
    let rawDigits := ((«machine»).jointGuess ib hb sb).symm rawPin
    let rowBounds : («dir₁»).DestinationBounds := by
      refine ⟨positiveTail,hg,posR,le_rfl,?_⟩
      simpa only [«dir₁»,«rTime»,«g₁»,freeDirectory,Directory.Layout.stride,Nat.add_sub_cancel,publicWidth] using
        gridRoom «actual» (show 0<«tiles» from Fintype.card_pos)
    let rows := NativeDemands.rows «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
    let recv := NativeDemands.receiver «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap» rowBounds
    let sizes := fun i : Fin rows.length => (rows[i.val]'i.isLt).width
    let priv := NativeDemands.privatePair «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
    let live := NativeDemands.livePair «finalN» cells₁ edge₁ port₁ «dir₁» «hosts₁» livePorts «dataGap»
    let ar := («task₁»).cube
    let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) p.cube.1)
    let decl := Prod.mk axis (fun (e : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (p.cube.2 e j))
    let label := meanPackedLabel «finalN» cells₁ recv sizes (List.finRange cells) ar.n ar.header.d (Nat.zero_lt_of_lt guard.two)
    let mass := declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv sizes
    let group := fun j : Fin ar.header.d => TeamNative.owner R mass j.val
    let owner := fun c : ℕ => if h:c<cells then group (label ⟨c,h⟩ axis) else 0
    let supply := Sum.elim (fun z : SuppliedWord «finalN» cells₁ => z.1) (id : Fin cells → Fin cells)
    let supplyBits := Sum.elim (supplyWidth «finalN» cells₁) (fun _ : Fin cells => «dataGap»)
    let sourceKey := numbered (reserveID (C:=cells) (suppliedID «finalN» cells₁ edge₁ port₁))
    let host := Sum.elim supply (cells₁ ∘ «hosts₁»)
    let fieldSize := Sum.elim supplyBits (fun _ : Fin («dir₁»).entries => «desc»)
    let ctl := controlsBase «origin» ar.cables ar.cells («dir₁»).entries ((«dir₁»).teams*(«dir₁»).sites)
    let pubAt := fun (_ : HeaderExterior wireLayout p.bits) u => («deployed»).publicWords u
    let libAt := fun z u => install SparseExterior.driver (lenPred+1) (nodes z u).start.routines
    let pinState := fun z u => (nodes z u).pins (rawDigits u)
    let regs := fun z u => (pinState z u).val.2.1
    let mems := fun z u => (pinState z u).val.2.2
    let observe := fun u => Pins.extendGuess (rawDigits u)
    let siteAt := fun (z : HeaderExterior wireLayout p.bits) (u : Fin (R+1)) =>
      SignedPrep.CandidateSite (X:=exteriorBudget) ar «dir₁» priv live p.cube owner decl group
        («early»).frame («early»).next ((«machine»).pinLayout u (ib u) (hb u) (sb u))
        ((«machine»).processorFields u pin z.val (ib u) (hb u) (sb u)) ((«machine»).transferFrame u wireLayout.header (dst u))
        (observe u) (pubAt z u) (libAt z u) (regs z u) (mems z u) host sourceKey fieldSize «finalN» cells₁ recv sizes
    let evidence := fun (z : HeaderExterior wireLayout p.bits) (u : Fin (R+1)) (site : siteAt z u) =>
      let g := rawDigits u
      let pk := reader.packetAt («place₀» u)
      let node := nodes z u
      let lib := install SparseExterior.driver (lenPred+1) node.start.routines
      let pub := («deployed»).publicWords u
      let bank := («deployed»).registers u
      let op := («early»).operands u «slot₁» pk
      let ad := («args₁») u
      let fs := («machine»).processorFields u pin z.val ad.ibase ad.hbase ad.starbase
      let init := processorMemory fs rw
      let bc := («machine»).transferFrame u ad.header ad.dst
      let time := jointBudget pk.bits.length rw+bc.readTicks+2+((pinSetup.slots+17*op.layout.count+1)+
        GeometryAdviceRate.ticks («tab»).size reserve «fullSize» packetWidth rw)
      let previous := routingExtension ((«task₁»).extension raw u.val rw (signedBudgetWords rw exteriorBudget)) «dir₁» «origin» ar.cables ar.cells
      ∃ (ret : Returns (withStartup pinGeometry) pub lib bank init),
        site.OnReturn previous «fresh» («tab»).size «fullSize» packetWidth «off» «stripeWidth» ctl
          (List.ofFn p.profile) (DiagonalTallyRAM.broadcast rw p.rawCounts) 0 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins g).val.1) (traceCost ret.val.1) ∧
        traceCost ret.val.1≤time ∧ ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn g ∧
        BootResidence (F:=fs) «early» u «slot₁» pk bc ad.advice pub lib p.bits init bank g ret.val.2.2 ∧
        PublishedPin «task₁» «dir₁» «finalN» cells₁ edge₁ port₁ «hosts₁» livePorts «early» u «slot₁» pk «origin» «dataGap» bc p.bits fs
          pub lib g (node.pins g).val.2.1 (node.pins g).val.2.2 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins g).val.1) (traceCost ret.val.1) ∧
        Image F₂ ((«s₁»).rows.site ∘ «hosts₁») (port₁ ∘ livePorts ∘ finProdFinEquiv.symm)
          ((source₂).eval input₁) «origin» (readings ret.val.2.2) ∧
        (∀ j : Fin 37, readings ret.val.2.2 (ctl+j.val)=(«task₁»).controls j.val) ∧
        ∀ i : Fin «fullSize», readings ret.val.2.2 («origin»+i.val)=emittedWords «aug» «order₁» fit «fullEmit» x «code₁» i
    declarationInRange p.cube → broadcastAllowed R exteriorBudget ar.header.blocks ar.b ar.K ar.h label recv sizes p.cube →
    ∃ sitesAt : ∀z u,siteAt z u, (∀z u,evidence z u (sitesAt z u)) ∧
      ∃ (wire : Routing.WireLayout (R+1) r link) (same : wire.header=wireLayout.header),
        let back := (HeaderExterior.changeLayout wireLayout wire same p.bits).symm
        let H := fun (z : HeaderExterior wire p.bits) u => (sitesAt (back z) u).receipt
        ∃ F : PreparationFrame «machine» wire ar decl p.bits pin (pubAt ∘ back) (libAt ∘ back) (regs ∘ back) (mems ∘ back),
          PreparationFrame.WriterProjection «machine» wire ar «dir₁» priv live owner decl group («early»).frame p.bits pin observe
            dst ib hb sb (pubAt ∘ back) (libAt ∘ back) (regs ∘ back) (mems ∘ back)
            (fun z u => (sitesAt (back z) u).epoch) (fun z u => (sitesAt (back z) u).published)
            (fun z u => (H z u).endReg) (fun z u => (H z u).out) (fun z u => (H z u).events) (fun z u => (H z u).history) F := by
  intro «G₀» «tiles» «w» «V» «extent» «header» «key» «fmt» «source» «seed₀» «compiled» «steps» «epochFormat» «aug» «base»
    «actual» «rTime» «s₁» «N₀» «code₁» «g₁» «p₁» «h₁» «finalN» «scp» «desc» «H₁» «J₁» «live₁» «dir₁» «publicDir» «boxes₁»
    «task₁» «ctrl₁» «dataArena» «dataStride» «dataGap» «hosts₁» «final₁» «priv₁» «reports₁» «tpl₁» «packetSize» «fullSize»
    «fullEmit» «gateCeiling» «order₁» «tab» «early» «gap» «fresh» «origin» «routed» «places» «pinned» «first» «off»
    «stripeWidth» «stripe» «place₀» «slot₁» «args₁» «deployed» «machine» «clockFrame» «pl» «portB» «ctlB» «loaded₁»
    «birth₁» «coefficient₁» «scalar₁» slope power coeff digitsChoice capChoice inputBounds numerals packetAddress gateFit
    geometryDest headerWidth fixed regions copiesFit wfit endFits memFit hw threeTeams hdrPos cap clock p pin rawPin
    encoded bufferExtent budgetFits room₀ cellsFit span rawRoom rs posR positiveTail privateTail localRoom globalRoom
    ctlBound wordRoom shortDescription teamCount guard sparse α ξ route budgetEq literalBound headerBound
    chosen certified exterior nodes ib hb sb dst rawDigits rowBounds rows recv sizes priv live ar axis decl label mass group owner
    supply supplyBits sourceKey host fieldSize ctl pubAt libAt pinState regs mems observe siteAt evidence valid allowed
  have inputs (z : HeaderExterior wireLayout p.bits) (u : Fin (R+1)) : ∃ site : siteAt z u, evidence z u site := by
    have produced :=  reader.deployed_frozen_raw_publication (physical:=physical) (P:=P) (basis:=basis) (machineFit:=machineFit) (W:=W) (position:=position)
      (sites:=sites) (edges:=edges) (ports:=ports) (plan:=plan) (wireLayout:=wireLayout) (x:=x) (seedTable:=seedTable)
      (wr:=wr) (hm:=hm) (seeds:=seeds) (number:=number) (widths:=widths) (ord:=ord) (fit:=fit) (count:=count)
      (cellNumber:=cellNumber) (vf:=vf) (cf:=cf) (hg:=hg) (short:=short) (pw:=pw) (extend:=extend) (room:=room)
      (hook:=hook) (histQ:=histQ) (hardwareTemplate:=hardwareTemplate) (sitePos:=sitePos) (cellPos:=cellPos)
      (ownerFits:=ownerFits) (gadgets:=gadgets) (digits:=digits) (ctrlFit:=ctrlFit) (hs:=hs) (hf:=hf) (keyFits:=keyFits)
      (sitesFit:=sitesFit) (keysFit:=keysFit) (sw:=sw) (pad:=pad) (dest:=dest) (hdr:=hdr) (bankLayout:=bankLayout)
      (bundleBits:=bundleBits) (shapes:=shapes) (U:=U) (deg:=deg) (exteriorBudget:=exteriorBudget)
      digitsChoice capChoice inputBounds numerals packetAddress gateFit geometryDest headerWidth fixed regions copiesFit wfit
      endFits memFit hw threeTeams hdrPos cap clock p pin (exterior z) z.property encoded bufferExtent budgetFits room₀ cellsFit span rawRoom
      rs posR positiveTail privateTail localRoom globalRoom ctlBound wordRoom shortDescription teamCount guard sparse route
    exact exists_comm.mp (produced u (rawDigits u) valid allowed)
  have pinRoom (u : Fin (R+1)) : («early»).frame+13 < ib u ∧
      ib u+((«machine»).pinLayout u (ib u) (hb u) (sb u)).count≤ar.header.header := by
    change («early»).frame+13 < («early»).ibase ∧ («early»).ibase+(«early»).count≤(«task₁»).cube.header.header
    have top : («early»).ibase+(«early»).count≤(«early»).next := by unfold StartupArena.next StartupArena.hbase; omega
    have lo : («early»).frame+13 < («early»).ibase := by unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense; omega
    exact ⟨lo,top.trans (by omega)⟩
  have candidates := signed_selected_candidates «machine» wireLayout p.bits (p.bits_length.trans headerWidth.symm) ar
    «dir₁» priv live pin observe dst ib hb sb («early»).frame («early»).next owner group p.cube pubAt libAt regs mems route
    host sourceKey fieldSize «finalN» cells₁ recv sizes
  rw [←budgetEq] at candidates
  exact candidates evidence inputs pinRoom (fun z => (certified z).choose_spec.choose) rfl rfl rfl literalBound headerBound valid


end Diagonal

end BorderVNP
end Computability
end OAI
