import OAI.Computability.BorderVNP.PackedFrozenPreparedPacket
import OAI.Computability.BorderVNP.PackedHistoryFrozenChosenPaths
import OAI.Computability.BorderVNP.PackedSignedBundleOutput

/-! # Cell and bundle output at a genuine return of the chosen signed program -/

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
open Diagonal DiagonalResidueRAM Branch TeamContraction.ProcessorSlots RoutingISA.Pins GeometryAdvice GeometryFrameEncoding
attribute [local instance] portFintype
set_option maxHeartbeats 12800000
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
local notation3 (prettyPrint := false) "rawState" => sewnPrograms N₀ lane₁ (h₁).bundle (fun _ : FreeBlock R tiles => g₁)
    (freeLane hg (gridRoom actual Fintype.card_pos)) (h₁).groupOwner ((h₁).groupAligned hg (gridRoom actual Fintype.card_pos))
    (s₁).rows.edge oldPort edge₁ port₁ prior₁
local notation3 (prettyPrint := false) "scp" => (epochFormat).schema.append
  (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*tiles) w)

open private oldWire staged_old from OAI.Computability.BorderVNP.PackedTerminalStagedFields
open private profilePaths_eq from OAI.Computability.BorderVNP.PackedHistoryChosenReservedGeometry

variable (dir : Directory.Layout) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (cellPos : 0 < cells) (ownerFits : k ≤ packetWidth)
local notation "H₁" => boundaryShape S (d+1) T
local notation "J₁" => (fan S)^T*tiles
local notation "live₁" => (R+1)*tiles
local notation "actualShape" => (⟨(H₁).sites,(H₁).edges+(p₁).slots⟩ : Shape)
local notation3 (prettyPrint := false) "publicDir" => {dir with sites := tiles, entries := J₁}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J₁ → Fin (H₁).sites)
local notation3 (prettyPrint := false) "roles₁" => (⟨(s₁).rows.site,edge₁⟩ : Rows actualShape finalN)
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d order position copies).edge
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "body₁" => fun j : Fin J₁ => W.seedStored position tag sites edges ports channels groups
  (order (finProdFinEquiv.symm j).2)
local notation3 (prettyPrint := false) "occupied₁" => fun i => oldWire (FinalTies.sewnPresent p₁ FinalTies.routePresent i)
local notation3 (prettyPrint := false) "keep₁" => Retained.Terminal.saved (X := σ) (reserve := reserve) epochFormat

variable {qbits tagCap control : ℕ} (arena stride gap desc gadgets digits : ℕ)
    (controls : Fin control → Fin (2^packetWidth))
local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((H₁).edges+(p₁).slots) live₁ packetWidth
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "signed₁" => SignedFields.liveFrame F₂ boxes₁ old₁ arena stride gap desc gadgets digits
local notation3 (prettyPrint := false) "feeds₁" => Terminal.feeds (s:=actualShape) F₂ occupied₁ (fun _ => true) boxes₁ hist₁ signed₁ (.inr true)
variable (hs : ∀ j, (((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).tags j).length≤tagCap) (hf : ∀ j, ((FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth).tags j).length≤tagCap)
    (keyFits : 60*logWidth r n≤qbits) (sitesFit : (boundaryShape S (d+1) T).sites<2^qbits)
    (keysFit : cells+1<2^k) (sw : ∀ j, ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))).width j≤packetWidth)
local notation3 (prettyPrint := false) "tpl₁" => template scp final₁ boxes₁ hs hf priv₁ reports₁
local notation3 (prettyPrint := false) "ptr₁" => (fun i : Fin J₁ => Sum.inl (Sum.inr i) : Fin J₁ → (tpl₁).Fields)
variable (pad : (roster (boundaryShape S (d+1) T).sites ((ProgramSchemas.epoch S (d+1) (60*logWidth r n) (Boundary.seedFormat G order position copies) T).schema.append
      (Sewn.schema (2*(boundaryShape S (d+1) T).edges+6*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) (60*logWidth r n))) (FinalTies.tieSchema ((boundaryShape S (d+1) T).edges+4*(R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d)
      ((R+1)*GridHosts.tileCount (Fintype.card (Cube D)) d) packetWidth)).length<2^qbits)
    (dest hdr : ℕ)
local notation3 (prettyPrint := false) "at₁" => Retained.packetBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁ control
local notation3 (prettyPrint := false) "packet₁" => (feeds₁).ordered scp final₁ boxes₁ hs hf priv₁ reports₁ keyFits keyFits sitesFit
  (Nat.lt_trans (Nat.lt_succ_self cells) keysFit) sw (fun _ => le_rfl) (fun _ => Fin.last cells) ptr₁ pad at₁ hdr
local notation3 (prettyPrint := false) "out₁" => frozenPacketEmitter (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls
  hs hf keyFits sitesFit keysFit sw pad dest hdr
local notation3 (prettyPrint := false) "read₁" => Sum.elim ((source₂).eval input₁) saved₁
local notation3 (prettyPrint := false) "cell₁" => TerminalTable.cell F₂ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "bit₁" => TerminalTable.bitStart F₂ ((source₂).eval input₁)
local notation3 (prettyPrint := false) "box₁" => TerminalTable.boxStart F₂ boxes₁ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "args₁" => (feeds₁).arguments read₁
local notation3 (prettyPrint := false) "directory₁" => directory scp final₁ boxes₁ hs hf priv₁ reports₁
  args₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁
local notation3 (prettyPrint := false) "field₁" => fun (i : Fin (roster (H₁).sites scp final₁).length) =>
  scalarArgs (cap := tagCap) scp final₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) bit₁ box₁ ((roster (H₁).sites scp final₁).get i)

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ) (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "banks" => ({bankLayout with cells := cells} : CellBanks.Layout)
local notation3 (prettyPrint := false) "bankValid" => VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)
local notation3 (prettyPrint := false) "bankSource" => BottomReports.BundleSort.source cells bundleBits
  (BottomReports.BundleSort.geometryHeaders F₂ old₁ desc (BottomReports.BundleSort.bankConfig banks gap bankValid) shapes)
local notation3 (prettyPrint := false) "packetSize" => signedGridOutputCount ((H₁).edges+4*(R+1)*tiles) cells J₁ live₁
  control (Total (tpl₁).publicDepth (tpl₁).chunkDepth)
local notation3 (prettyPrint := false) "fullSize" => packetSize+(2^bundleBits+2^bundleBits)
local notation3 (prettyPrint := false) "fullEmit" => frozenPacketWithBundles (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend dir number sitePos ownerFits arena stride gap desc gadgets digits controls hs hf
  keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes

variable {scalar : Type} [Fintype scalar] {supplement : scalar → K} {characteristic lenPred candidate : ℕ}
    {order₂ : Fin (lenPred+1) × Bool ≃ Fin (2*(lenPred+1))}
    {field : CommonField e supplement characteristic lenPred candidate order₂} {chart : AdvisedBranch field}
    [Fact field.p.Prime] [Algebra (ZMod field.p) chart.E] {mult tally wordBits pinWidth pc regs routines spare sortExp : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally wordBits pinWidth)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc regs 32 routines)
    (data : SiteData R r regs 32 wordBits spare) (fitSite : fitsWith physical regs 32 r wordBits spare R ell n sortExp)
    (valuation entry totals : Fin (R+1) → ℕ) (old : Fin (R+1) → Fin 81 → Word wordBits)
    (wireLayout : Routing.WireLayout (R+1) r ell) (ceiling : ℕ)
    (bootStripe : GeometryAdvice.Stripe) (bootBits : Fin (R+1) → List Bool)
    (descriptors : Fin dir.entries → Fin dir.description → Bool)
    {cubeAxes symbols cap claimsDim : ℕ} (rawHeader : JointHeader.PositiveFields reserve cubeAxes symbols cap (R+1) claimsDim tally)
local notation "pinCount" => (pairedTableParameters (lenPred+1) candidate+2)*pinWidth
local notation3 (prettyPrint := false) "early" => reader.startupArenaWith (n:=n) (reg:=regs) physical spare ell wireLayout.header
local notation3 (prettyPrint := false) "fresh" => (early).next+7*dir.candidates
local notation3 (prettyPrint := false) "order₁" => broadcastOrder (fan S) widths ord T
local notation3 (prettyPrint := false) "tab" => reservedGeometryTable aug order₁ fit fullEmit x ceiling
local notation3 (prettyPrint := false) "off" => (early).literal/4
local notation3 (prettyPrint := false) "stripeWidth" => GeometryAdviceRate.stripeWidth
  (GeometryOutput.packetCount reserve (Table.size tab) fullSize packetWidth*wordBits) r
local notation3 (prettyPrint := false) "stripe" => Allocation.stripe fresh reserve (Table.size tab) fullSize packetWidth off stripeWidth
local notation3 (prettyPrint := false) "ext" => fun u : Fin (R+1) =>
  Allocation.fields (old u) fresh reserve (Table.size tab) fullSize packetWidth off stripeWidth
local notation3 (prettyPrint := false) "place" => fun u : Fin (R+1) =>
  ReaderPlacement.inArena early (valuation u) (entry u) (totals u) (ext u)
local notation3 (prettyPrint := false) "geomBits" => fun _ : Fin (R+1) => GeometryAdvice.serialized (GeometryAdvice.packet («w» := wordBits)
  fresh (Allocation.packed fresh reserve (Table.size tab) fullSize packetWidth wordBits) tab
  (fun i => (early).broadcastBase+1+Fin.val i))
local notation3 (prettyPrint := false) "site" => reader.startupSitesWith physical P data place fitSite dir bootStripe stripe
  bootBits geomBits descriptors wireLayout.header
local notation3 (prettyPrint := false) "linkWiring" => wiringWith physical P site pinCount ell n sortExp fitSite

include pw room hook in
/-- Every return from the selected program on this shared header publishes the
real cell packet, routing and sorted bundle banks for exactly its original history. -/
theorem frozen_chosen_packet
    (sizeFit : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c < 2^packetWidth)
    (countRoom : ∀ c, guessedSize finalN cells₁ c+siteSize finalN cells₁ c (fun v => (rawState v).program.size)
      +suppliedSize finalN cells₁ c+gadgets*digits ≤ 2^packetWidth)
    (wide : 2^(tpl₁).recordDepth≤2^(packetWidth+k))
    (boxRoom : (∑ i, (boxes₁ i).length)<2^packetWidth)
    (rowRoom : (scp).rows.length+(final₁).rows.length<2^packetWidth)
    (capRoom : tagCap<2^packetWidth) (three : 3<2^packetWidth)
    (known : ∀ i t, t∈boxWords (boxes₁ i) → t<2^packetWidth)
    (reportRows : ∀ c, (reports₁ c).length<2^packetWidth)
    (vectors : ∀ c r, r∈reports₁ c → r.length<2^packetWidth)
    (limit : Fin cells → ℕ) (limitRoom : ∀ c, limit c<2^packetWidth)
    (bounds : ∀ c : Fin cells, ∀ r ∈ (FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val)
      (s₁).rows.site edge₁ port₁ (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc)).records,
      RecordFields r (limit c))
    (bufferRoom : at₁+2^(tpl₁).publicDepth<2^packetWidth) (descRoom : 2^(tpl₁).chunkDepth≤2^packetWidth) (headerRoom : hdr<2^packetWidth)
    (gateFit : (geometryTable aug order₁ fit fullEmit x).size≤ceiling)
    (geometryDest : Allocation.dest fresh reserve ceiling fullSize packetWidth=dest)
    (lenFits : rawHeader.bits.length=wireLayout.header) (wire : HeaderExterior wireLayout rawHeader.bits)
    (u : Fin (R+1)) (pin : Fin pinCount → Bool) (mac : TeamOpcode.Macros wordBits 8) (bank : RoutingISA.Bank wordBits)
    (regions : JointRoom dir (freeStartWith physical r 32 regs wordBits n) spare bootStripe stripe)
    (copiesFit : reader.packetBitCount≤r) (wfit : packetWidth≤wordBits)
    (endFits : Allocation.stop fresh reserve ceiling fullSize packetWidth wordBits<2^wordBits) (encoded : code₁=rawHeader.profile) :
    let op := reader.siteOperandsWith physical P data place fitSite wireLayout.header u
    let pk := reader.packetAt (place u)
    let pub := (site).publicWords u
    let fs := (linkWiring).processorFields u pin wire.val op.layout.ibase op.layout.hbase op.layout.starbase
    let bc := (linkWiring).transferFrame u wireLayout.header op.broadcastBase
    let initial := RAMMemory.initialMemory fs.header.length (TeamTapeInputEmit.headerWord wordBits fs.header)
    let timeBound := jointBudget pk.bits.length wordBits+bc.readTicks+2+
      ((pinSetup.slots+17*op.layout.count+1)+GeometryAdviceRate.ticks ceiling reserve fullSize packetWidth wordBits)
    let arg := adviceOffsetWith physical r 32 regs wordBits n
    ∃ pf : Pins.ProcessorFields ((early).operands u arg pk).layout,
      ProfilePaths (withStartup pinGeometry) op.layout.guessWidth pub mac bank initial True timeBound dest
        (emittedWords aug order₁ fit fullEmit x code₁) (BootResidence (F:=pf) early u arg pk bc op.advice pub mac
          rawHeader.bits initial bank) ∧
      ∀ ret : Returns (withStartup pinGeometry) pub mac bank initial, let ram := readings ret.val.2.2
        Image F₂ old₁ id ((source₂).eval input₁) dest ram ∧
          (∀ i : Fin control, ram (controlsBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁+i.val)=(controls i).val) ∧
          Published directory₁ (tpl₁).publicDepth (tpl₁).chunkDepth at₁ hdr ptr₁ ((tpl₁).arguments args₁ field₁) ram ∧
          (∀ i : Fin (2^bundleBits+2^bundleBits), ram (dest+packetSize+i.val) = value (fun h =>
            (CellPacketGeometry.geometry bankSource).eval ((source₂).eval input₁) (.inl (i,h)))) ∧
          ∀ c : Fin cells,
            ((directory₁).privateWires c.castSucc = FinalCell.privateBits finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val ∧
             (directory₁).reports c.castSucc = DiagonalTallyCellReports.countFields
               (FinalCell.countBase finalN (fun v => (cells₁ v).val) (fun v => (rawState v).program) c.val) gadgets digits) ∧
            ∀ slot pb db eb scratch burst bytes,
              ((directory₁).placed c.castSucc hdr slot body₁ pb db eb scratch burst bytes).directory =
                FinalCell.directory (fun i => (cell₁ i).val) finalN (fun v => (cells₁ v).val) (s₁).rows.site edge₁ port₁
                  (fun v => (rawState v).program) c.val ((directory₁).reports c.castSucc) := by
  intro op pk pub fs bc initial timeBound arg
  obtain ⟨pf,all⟩ := reader.frozen_profile_chosen_paths physical P data fitSite valuation entry totals old wireLayout
    plan G order position W tag sites edges ports table x wr hm widths ord fit fullEmit dir ceiling bootStripe bootBits
    descriptors rawHeader gateFit lenFits wire u pin mac bank regions copiesFit wfit endFits q encoded
  have moved := profilePaths_eq all Iff.rfl rfl geometryDest rfl
  refine ⟨pf,moved,?_⟩
  intro ret ram
  have split := ProfilePaths.split_headerBanks aug order₁ fit x code₁ out₁ source₂ banks F₂ old₁ desc gap shapes bankValid moved
  obtain ⟨img,controlsAt,published,content⟩ := plan.frozen_prepared_packet G order position W tag sites edges ports
    table x wr hm seeds number widths ord fit actual count cellNumber vf cf hg short pw extend room hook q dir
    sitePos cellPos ownerFits arena stride gap desc gadgets digits controls hs hf keyFits sitesFit keysFit sw pad dest hdr
    sizeFit countRoom wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom bounds bufferRoom
    descRoom headerRoom wfit split.1 ret
  exact ⟨img,controlsAt,published,split.2 ret,content⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
