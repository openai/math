import OAI.Computability.BorderVNP.PackedFrozenChosenPacket
import OAI.Computability.BorderVNP.PackedFrozenDirectoryPublication
import OAI.Computability.BorderVNP.DiagonalNativeTimedArena

/-! # Publishing the chosen frozen packet on its original signed physical pin -/

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
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
set_option backward.isDefEq.respectTransparency false

private theorem before_publication_room (a : StartupArena) {gap reserve gates outputs bits hw : ℕ}
    (room : Allocation.stop (a.next+gap) reserve gates outputs bits hw<2^hw) : a.next<2^hw ∧ 1<2^hw := by
  have head_le (fresh u k o b w : ℕ) : fresh ≤ Allocation.stop fresh u k o b w := by
    unfold Allocation.stop Allocation.packed Allocation.dense Allocation.dest Allocation.temp
    omega
  have first := (Nat.le_add_right a.next gap).trans_lt ((head_le _ _ _ _ _ _).trans_lt room)
  exact ⟨first,(show 1≤a.next by rw [StartupArena.next_eq]; omega).trans_lt first⟩

private theorem header_positive {reserve c group cap teams num bits n : ℕ}
    (p : JointHeader.PositiveFields reserve c group cap teams num bits) (length : p.bits.length=n) : 0<n := by
  rw [←length,p.bits_length]
  unfold JointHeader.PositiveFields.width
  omega

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
local notation "mass" => initialMass (D:=D) n r d copies headerFactor
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

variable (hardwareTemplate : SignedTaskArena.Layout) (desc : ℕ) (sitePos : 0 < (boundaryShape S (d+1) T).sites)
    (cellPos : 0 < cells) (ownerFits : k ≤ packetWidth)
local notation "H₁" => boundaryShape S (d+1) T
local notation "J₁" => (fan S)^T*tiles
local notation "live₁" => (R+1)*tiles
local notation3 (prettyPrint := false) "dir₁" => freeDirectory R r (actual.program.length+rTime) ell tiles g₁ J₁ desc
local notation "actualShape" => (⟨(H₁).sites,(H₁).edges+(p₁).slots⟩ : Shape)
local notation3 (prettyPrint := false) "publicDir" => {(dir₁) with sites := tiles, entries := J₁}
local notation3 (prettyPrint := false) "boxes₁" => scheduledBoxes publicDir rfl number sitePos
local notation3 (prettyPrint := false) "old₁" => (originalPins sitePos offs : Fin J₁ → Fin (H₁).sites)
local notation3 (prettyPrint := false) "roles₁" => (⟨(s₁).rows.site,edge₁⟩ : Rows actualShape finalN)
local notation3 (prettyPrint := false) "channels" => (groupedGridRows G axes d order position copies).edge
local notation "groups" => Equiv.toEmbedding (Equiv.refl (Fin tiles))
local notation3 (prettyPrint := false) "body₁" => fun j : Fin J₁ => W.seedStored position tag sites edges ports channels groups
  (order (finProdFinEquiv.symm j).2)
local notation3 (prettyPrint := false) "occupied₁" => fun i => oldWire (FinalTies.sewnPresent p₁ FinalTies.routePresent i)
local notation3 (prettyPrint := false) "keep₁" => Retained.Terminal.saved (X := σ) (reserve := reserve) epochFormat

local notation3 (prettyPrint := false) "task₁" => hardwareTemplate.withNetwork cells ((H₁).edges+(p₁).slots)
variable {qbits tagCap : ℕ} (gadgets digits : ℕ)
    (ctrlFit : ∀ i : Fin 37, (hardwareTemplate.withNetwork cells ((boundaryShape S (d+1) T).edges+
      4*(R+1)*(GridHosts.tileCount (Fintype.card (Cube D)) d))).controls i.val < 2^packetWidth)
local notation3 (prettyPrint := false) "ctrl₁" => fun i : Fin 37 => (⟨(task₁).controls i.val,ctrlFit i⟩ : Fin (2^packetWidth))
local notation3 (prettyPrint := false) "dataArena" => (task₁).cube.cellBank
local notation3 (prettyPrint := false) "dataStride" => (task₁).cube.cellStride
local notation3 (prettyPrint := false) "dataGap" => (task₁).p.privateGap
local notation3 (prettyPrint := false) "hosts₁" => originalDescriptionRows plan.compiled.machine seed₀ q dir₁ rfl order
local notation3 (prettyPrint := false) "livePorts" => Function.Embedding.refl (Fin (R+1) × Fin tiles)

local notation3 (prettyPrint := false) "final₁" => FinalTies.tieSchema ((H₁).edges+(p₁).slots) live₁ packetWidth
local notation3 (prettyPrint := false) "priv₁" => FinalReports.Spare.priv (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "reports₁" => FinalReports.Spare.reports (C:=cells) (g:=gadgets) (digits:=digits) (E:=Fin J₁)
local notation3 (prettyPrint := false) "signed₁" => SignedFields.liveFrame F₂ boxes₁ old₁ dataArena dataStride dataGap desc gadgets digits
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
local notation3 (prettyPrint := false) "at₁" => Retained.packetBase dest ((H₁).edges+(p₁).slots) cells J₁ live₁ 37
local notation3 (prettyPrint := false) "packet₁" => (feeds₁).ordered scp final₁ boxes₁ hs hf priv₁ reports₁ keyFits keyFits sitesFit
  (Nat.lt_trans (Nat.lt_succ_self cells) keysFit) sw (fun _ => le_rfl) (fun _ => Fin.last cells) ptr₁ pad at₁ hdr
local notation3 (prettyPrint := false) "out₁" => frozenPacketEmitter (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend (dir₁) number sitePos ownerFits dataArena dataStride dataGap desc gadgets digits ctrl₁
  hs hf keyFits sitesFit keysFit sw pad dest hdr
local notation3 (prettyPrint := false) "read₁" => Sum.elim ((source₂).eval input₁) saved₁
local notation3 (prettyPrint := false) "cell₁" => TerminalTable.cell F₂ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "bit₁" => TerminalTable.bitStart F₂ ((source₂).eval input₁)
local notation3 (prettyPrint := false) "box₁" => TerminalTable.boxStart F₂ boxes₁ cellPos ((source₂).eval input₁)
local notation3 (prettyPrint := false) "args₁₀" => (feeds₁).arguments read₁
local notation3 (prettyPrint := false) "directory₁" => directory scp final₁ boxes₁ hs hf priv₁ reports₁
  args₁₀ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) cell₁ bit₁ box₁
local notation3 (prettyPrint := false) "field₁" => fun (i : Fin (roster (H₁).sites scp final₁).length) =>
  scalarArgs (cap := tagCap) scp final₁ ((hist₁).eval read₁) ((feeds₁).binding.eval read₁) bit₁ box₁ ((roster (H₁).sites scp final₁).get i)

variable (bankLayout : CellBanks.Layout) (bundleBits : ℕ) (shapes : Fin ((fan S)^T*GridHosts.tileCount (Fintype.card (Cube D)) d) → BottomReports.BundleSort.Shape)
local notation3 (prettyPrint := false) "banks" => ({bankLayout with cells := cells} : CellBanks.Layout)
local notation3 (prettyPrint := false) "bankValid" => VPVNP.VerifierNetwork.Frame.initial (fun _ : Unit => Sum.inr true)
local notation3 (prettyPrint := false) "bankSource" => BottomReports.BundleSort.source cells bundleBits
  (BottomReports.BundleSort.geometryHeaders F₂ old₁ desc (BottomReports.BundleSort.bankConfig banks dataGap bankValid) shapes)
local notation3 (prettyPrint := false) "packetSize" => signedGridOutputCount ((H₁).edges+4*(R+1)*tiles) cells J₁ live₁
  37 (Total (tpl₁).publicDepth (tpl₁).chunkDepth)
local notation3 (prettyPrint := false) "fullSize" => packetSize+(2^bundleBits+2^bundleBits)
local notation3 (prettyPrint := false) "fullEmit" => frozenPacketWithBundles (reserve := reserve) S G order position σ actual
  count cellNumber vf cf hg short extend (dir₁) number sitePos ownerFits dataArena dataStride dataGap desc gadgets digits ctrl₁ hs hf
  keyFits sitesFit keysFit sw pad dest hdr bankLayout bundleBits shapes

variable {scalar : Type} [Fintype scalar] {supplement : scalar → K} {characteristic lenPred candidate : ℕ}
    {order₂ : Fin (lenPred+1) × Bool ≃ Fin (2*(lenPred+1))}
    {field : CommonField e supplement characteristic lenPred candidate order₂} {chart : AdvisedBranch field}
    [Fact field.p.Prime] [Algebra (ZMod field.p) chart.E] {mult tally wordBits pinWidth pc routines spare sortExp : ℕ}
    (reader : ChosenReader chart (R+1) r mult tally wordBits pinWidth)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
    (data : SiteData R r 64 32 wordBits spare) (fitSite : fitsWith physical 64 32 r wordBits spare R ell n sortExp)
    (valuation entry totals : Fin (R+1) → ℕ) (old : Fin (R+1) → Fin 81 → Word wordBits)
    (wireLayout : Routing.WireLayout (R+1) r ell) (ceiling : ℕ)
    (bootStripe : GeometryAdvice.Stripe) (bootBits : Fin (R+1) → List Bool)
    (descriptors : Fin ((fan S)^T*(GridHosts.tileCount (Fintype.card (Cube D)) d)) → Fin desc → Bool)
    {cubeAxes symbols cap claimsDim : ℕ} (rawHeader : JointHeader.PositiveFields reserve cubeAxes symbols cap (R+1) claimsDim tally)
local notation "pinCount" => (pairedTableParameters (lenPred+1) candidate+2)*pinWidth
local notation3 (prettyPrint := false) "early" => reader.startupArenaWith (n:=n) (reg:=64) physical spare ell wireLayout.header
local notation3 (prettyPrint := false) "fresh" => (early).next+7*(dir₁).candidates
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
local notation3 (prettyPrint := false) "site" => reader.startupSitesWith physical P data place fitSite (dir₁) bootStripe stripe
  bootBits geomBits descriptors wireLayout.header
local notation3 (prettyPrint := false) "linkWiring" => wiringWith physical P site pinCount ell n sortExp fitSite


open CellMacro.Generator RoutingISA.CompactMachine
variable (gen : Fragment CellMacro.Generator.IO) (operandBase : Arg → Word wordBits) (previous : Fin 81 → Word wordBits)
    (raw team subtotalWidth bufferExtent : ℕ)
local notation3 (prettyPrint := false) "mac₀" => install gen n (TeamSiteEvents.macros («w»:=wordBits) (siteLibrary gen) (nativeClock n))
local notation3 (prettyPrint := false) "slot₁" => adviceOffsetWith physical r 32 64 wordBits n
local notation3 (prettyPrint := false) "args₁" => fun z : Fin (R+1) => (early).unitAddresses slot₁ (reader.packetAt (place z))
local notation3 (prettyPrint := false) "portB" => bases dest (task₁).cube.cables cells J₁
local notation3 (prettyPrint := false) "placeB" => privateLayout (early).frame dest (task₁).cube.cables cells J₁ desc dataGap
local notation3 (prettyPrint := false) "ctlB" => controlsBase dest (task₁).cube.cables cells J₁ live₁

local notation "loaded₁" => S.publicProgramFactor^T*initialMass (D:=D) n r d copies headerFactor
local notation "birth₁" => max 2 (max copies (seedBoxCapacity n r axes d (Fintype.card (Direction axes))))
local notation "coefficient₁" => (birthWordCoefficient e+8)*(BankCharges.bound e+1)*(S.populationFactor+2)
local notation "scalar₁" => max (15*loaded₁) (H₁).sites +
    max (max birth₁ (coefficient₁*(loaded₁+1))) (max 1 (15*loaded₁))+1

include pw room hook in
set_option maxHeartbeats 64000000 in
/-- On a positive shared input bearing the original history code, the concrete
emitted cell and bundle packet drives the real directory publication. The
chosen trace, stored descriptions, receiver keys and all physical controls
refer to the same initial verifier and the same returned pin. -/
theorem frozen_chosen_publication {slope power coeff : ℕ}
    (digitsChoice : digits=packetWidth) (capChoice : tagCap=ProgramSchemas.signedTagCapacity (e:=e))
    (inputBounds : Diagonal.SignedPacketInputBounds S (d+1) T cells live₁ w packetWidth slope power coeff gadgets fmt publicDir rfl number)
    (numerals : Diagonal.FrozenPacketNumerals e number gadgets hdr packetWidth scalar₁ loaded₁)
    (installedGrid : (seed₀).val.pack.layout = (wiredGrid actual axes d order position).groupedRepeat
      (fun _ : Fin tiles => GridHosts.inputBlockWidth r n axes d) order copies)
    (packetAddress : Allocation.stop fresh reserve ceiling fullSize packetWidth packetWidth<2^packetWidth)
    (gateFit : (geometryTable aug order₁ fit fullEmit x).size≤ceiling)
    (geometryDest : Allocation.dest fresh reserve ceiling fullSize packetWidth=dest)
    (lenFits : rawHeader.bits.length=wireLayout.header) (wire : HeaderExterior wireLayout rawHeader.bits)
    (u : Fin (R+1)) (pin : Fin pinCount → Bool)
    (regions : JointRoom (dir₁) (freeStartWith physical r 32 64 wordBits n) spare bootStripe stripe)
    (copiesFit : reader.packetBitCount≤r) (wfit : packetWidth≤wordBits)
    (endFits : Allocation.stop fresh reserve ceiling fullSize packetWidth wordBits<2^wordBits) (encoded : code₁=rawHeader.profile)
    (hardwareLit : actual.program.length+rTime=(early).literal)
    (node : BootedPinStart gen linkWiring (site).publicWords (site).registers args₁ pin wire.val u)
    (guess : Fin ((linkWiring).pinLayout u (args₁ u).ibase (args₁ u).hbase (args₁ u).starbase).guessWidth → Bool)
    (pubEq : (site).publicWords u=((early).operands u slot₁ (reader.packetAt (place u))).bank
      (core (withDemandBase ((task₁).routeBank (early).frame operandBase) (early).next) dest (task₁).cube.cables cells))
    (installed : (reader.packetAt (place u)).extension=signedProfileExtension task₁ previous (dir₁) dest (task₁).cube.cables cells
      raw team subtotalWidth fresh reserve ceiling fullSize packetWidth off stripeWidth)
    (room₀ : (task₁).cube.stop<2^wordBits) (cellsFit : cells≤2^wordBits)
    (span : (early).next+7*(dir₁).candidates≤dest) (rawRoom : (early).next+7*(dir₁).candidates≤(task₁).cube.header.header)
    (rs : r≤tiles) (posR : 0<r) (positiveTail : 0<(actual.program.length+rTime)/2)
    (tail : J₁*desc≤(R+1)*r*((actual.program.length+rTime)/2))
    (localRoom : ∀ c,suppliedSize finalN cells₁ c+dataGap+(∑ j,if cells₁ (hosts₁ j)=c then desc else 0)≤(task₁).cube.cellStride)
    (globalRoom : ∀ c,suppliedSize finalN cells₁ c+dataGap+J₁*desc≤bufferExtent)
    (ctl : ctlB+8<2^wordBits)
    (wordRoom : Directory.ISA.wordBound (Directory.ISA.placementBound (dir₁) (placeB).raw (portB).livePairs bufferExtent)<2^wordBits) :
    let op := reader.siteOperandsWith physical P data place fitSite wireLayout.header u
    let pk := reader.packetAt (place u)
    let pub := (site).publicWords u
    let fs := (linkWiring).processorFields u pin wire.val op.layout.ibase op.layout.hbase op.layout.starbase
    let bc := (linkWiring).transferFrame u wireLayout.header op.broadcastBase
    let initial := RAMMemory.initialMemory fs.header.length (TeamTapeInputEmit.headerWord wordBits fs.header)
    let timeBound := jointBudget pk.bits.length wordBits+bc.readTicks+2+
      ((pinSetup.slots+17*op.layout.count+1)+GeometryAdviceRate.ticks ceiling reserve fullSize packetWidth wordBits)
    let arg := adviceOffsetWith physical r 32 64 wordBits n
    ∃ pf : Pins.ProcessorFields ((early).operands u arg pk).layout, HEq pf fs ∧
      ProfilePaths (withStartup pinGeometry) op.layout.guessWidth pub mac₀ ((site).registers u) initial True timeBound dest
        (emittedWords aug order₁ fit fullEmit x code₁) (BootResidence (F:=pf) early u arg pk bc op.advice pub mac₀
          rawHeader.bits initial ((site).registers u)) ∧
      ∃ ret : Returns (withStartup pinGeometry) pub mac₀ ((site).registers u) initial,
        ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn guess ∧ traceCost ret.val.1≤timeBound ∧
        BootResidence (F:=pf) early u arg pk bc op.advice pub mac₀ rawHeader.bits initial ((site).registers u) guess ret.val.2.2 ∧
        (∀ i : Fin 37, readings ret.val.2.2 (ctlB+i.val)=(task₁).controls i.val) ∧
        PublishedPin task₁ dir₁ finalN cells₁ edge₁ port₁ hosts₁ livePorts early u arg pk dest dataGap bc rawHeader.bits pf
          pub mac₀ guess (node.pins guess).val.2.1 (node.pins guess).val.2.2 ret.val.2.1 ret.val.2.2
          (node.used+traceCost (node.pins guess).val.1) (traceCost ret.val.1) ∧
        let ram := readings ret.val.2.2
        Image F₂ ((s₁).rows.site ∘ hosts₁) (port₁ ∘ livePorts ∘ finProdFinEquiv.symm)
          ((source₂).eval input₁) dest ram ∧
          Published directory₁ (tpl₁).publicDepth (tpl₁).chunkDepth at₁ hdr ptr₁ ((tpl₁).arguments args₁₀ field₁) ram ∧
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
  obtain ⟨sizeFit,countRoom,wide,boxRoom,rowRoom,capRoom,three,known,reportRows,vectors,
    limit,limitRoom,bounds,bufferRoom,descRoom,headerRoom⟩ :=
    plan.frozen_packet_operands G order position W tag sites edges ports table x wr hm seeds number widths ord fit
      actual count cellNumber vf cf hg short pw extend room hook q dir₁ sitePos cellPos
      dataArena dataStride dataGap desc gadgets digits hs hf dest hdr
      digitsChoice capChoice rfl inputBounds numerals installedGrid fresh ceiling bundleBits geometryDest packetAddress
  obtain ⟨_,_,read⟩ := plan.frozen_chosen_packet G order position W tag sites edges ports table x wr hm seeds number
    widths ord fit actual count cellNumber vf cf hg short pw extend room hook q dir₁ sitePos cellPos ownerFits
    dataArena dataStride dataGap desc gadgets digits ctrl₁ hs hf keyFits sitesFit keysFit sw pad dest hdr bankLayout
    bundleBits shapes reader physical P data fitSite valuation entry totals old wireLayout ceiling bootStripe bootBits
    descriptors rawHeader sizeFit countRoom wide boxRoom rowRoom capRoom three known reportRows vectors limit limitRoom
    bounds bufferRoom descRoom headerRoom gateFit geometryDest lenFits wire u pin mac₀ ((site).registers u)
    regions copiesFit wfit endFits encoded
  obtain ⟨pf,sameF,atSite⟩ := reader.frozen_profile_chosen_paths_physical physical P data fitSite valuation entry totals old
    wireLayout plan G order position W tag sites edges ports table x wr hm widths ord fit fullEmit dir₁ ceiling
    bootStripe bootBits descriptors rawHeader gateFit lenFits wire u pin mac₀ ((site).registers u)
    regions copiesFit wfit endFits q encoded
  have all := profilePaths_eq atSite Iff.rfl rfl geometryDest rfl
  obtain ⟨ceilFit,one⟩ := before_publication_room (gap := 7*(dir₁).candidates) (reserve := reserve)
    (gates := ceiling) (outputs := fullSize) (bits := packetWidth) early endFits
  have positive := header_positive rawHeader lenFits
  have actualOps := reader.siteOperands_arenaWith physical P data fitSite valuation entry totals ext wireLayout u
  have opFits := (reader.arena_fitsWith physical P data fitSite valuation entry totals ext wireLayout u positive
    copiesFit ceilFit).1
  have ready := (congrArg (fun a : PacketOperands => a.Fits wordBits) actualOps).mp opFits
  obtain ⟨ret,spelling,cost,resident,controlsAt,published⟩ := plan.frozen_profile_publication G order position W tag sites
    edges ports table x wr hm seeds number widths ord fit actual count cellNumber vf cf hg short pw extend room hook q
    hardwareTemplate desc node early u arg pk rawHeader.bits pf op.advice operandBase previous dest dataGap bufferExtent
    raw team subtotalWidth fresh reserve ceiling fullSize packetWidth off stripeWidth guess sitePos sizeFit all
    (fun ret => ⟨(read ret).1,(read ret).2.1⟩) pubEq installed ready room₀ one ownerFits wfit cellPos cellsFit span
    rawRoom rfl rfl hardwareLit rfl rs posR positiveTail tail localRoom globalRoom ctl wordRoom rfl lenFits
    (SignedTaskArena.Layout.consumer_words task₁).2.1
  have actualImage := plan.frozen_routing_image G order position W tag sites edges ports table x q dir₁ sitePos F₂
    ((source₂).eval input₁) dest (readings ret.val.2.2) (read ret).1
  exact ⟨pf,sameF,all,ret,spelling,cost,resident,controlsAt,published,actualImage,(read ret).2.2⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
