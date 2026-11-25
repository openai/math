import OAI.Computability.BorderVNP.DiagonalIssuedReportDataFromHistory
import OAI.Computability.BorderVNP.DiagonalIssuedDeliveryGeometry
import OAI.Computability.BorderVNP.PackedNativeDemandLabels
import OAI.Computability.BorderVNP.DiagonalSupportedSeedRoster

/-! # The complete sparse report input from one physical writer and the frozen VNP seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

open BorderVNP.Cube.Physical BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacketGeometry CellDispatch Packing.BundleDirectory
open DiagonalTallyCellReports.ReportDirectory

open TeamContraction BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator

variable {teams n w : ℕ} (a : SignedTaskArena.Layout)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix a.id)

local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "frame" => ((U agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits a.id U p
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

variable {fit : (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2)).Fits w
      (readings (PinStart.visits a.id U p).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
      (PinStart.visits a.id U p).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits a.id U p).reports.val.2.2))
        (PinStart.visits a.id U p).reports.val.2.2 data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=agent.val) («frame»:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

open CellPacketGeometry.History CellPacketGeometry.History.Native Packing.Inherited FrozenTape
open Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open TeamContraction.ProcessorSlots TeamContraction ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open Packing.DeckGrid Cover Packing.BottomReports Diagonal.ExternalSew

variable {netDim siteCount portCount axes keyBits digits₀ : ℕ} {P σ E : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    (net : Network netDim P bits) (host : net.Site → Fin a.cube.cells) (aux : net.Site → ℕ)
    (siteID : net.Site ↪ Fin siteCount) (edgeID : net.Edge ↪ Fin a.cube.cables) (portID : P ↪ Fin portCount)
    (fieldData : Fields siteCount a.cube.cables portCount a.cube.cells axes keyBits digits₀ σ) (x : σ → Bool)
    (original : Fin dir.entries ↪ net.Site) (livePorts : (Fin dir.teams × Fin dir.sites) ↪ P)
    (bounds : dir.DestinationBounds) (origin loadBase gap : ℕ) (profile placed : Memory w)
local notation3 (prettyPrint := false) "nativeRows" => NativeDemands.rows net host edgeID portID dir original livePorts gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver net host edgeID portID dir original livePorts gap bounds
local notation3 (prettyPrint := false) "incoming" => fun i : Fin (nativeRows).length => (nativeRows)[i.val].width
local notation3 (prettyPrint := false) "pp" => Directory.ISA.placement (readings placed)
  (bases origin a.cube.cables a.cube.cells dir.entries).privatePairs
local notation3 (prettyPrint := false) "lp" => Directory.ISA.placement (readings placed)
  (bases origin a.cube.cables a.cube.cells dir.entries).livePairs
local notation3 (prettyPrint := false) "published" => readings (Directory.ISA.publish placed frame loadBase (dir.directory pp lp))
local notation3 (prettyPrint := false) "ord" => NativeDemands.cableOrder net host edgeID
local notation3 (prettyPrint := false) "home" => fun j : Fin dir.entries => host (original j)

variable {r t pinCount link inner k states seedDim seedAxes depth leaves copies : ℕ} {Edge : Type} [Fintype Edge]
    {wiring : Wiring teams r t pinCount link inner (k+1) Edge}
    {gridOrder : Fin (Fintype.card (Fin seedAxes → Deck (depth+2))) ≃ (Fin seedAxes → Deck (depth+2))}
    {state : ParseTable.State (Fin (k+1) × Bool) states} (W : WiredWitness wiring (Fin.last k) seedDim seedAxes depth gridOrder state)
    (pos : (Fin seedAxes → Deck (depth+2)) → {dv : EuclideanSpace ℝ (Fin seedDim) // ‖dv‖≤1})
    (sourceOrder : Fin dir.entries ≃ Fin leaves × (Fin seedAxes → Deck (depth+2)))
    (code : GrammarLabel (Fin (k+1) × Bool) (ParseTable.State (Fin (k+1) × Bool) states) (k+1) ↪ ℕ)
    {ss se sp sc sg : ℕ} (sites₀ : (W.routedFine pos).Site ↪ Fin ss) (edges₀ : (W.routedFine pos).Edge ↪ Fin se)
    (ports₀ : Fin r × Fin (publicWidth wiring) ↪ Fin sp)
    (channels : ((Fin seedAxes → Deck (depth+2)) × Direction seedAxes) ↪ Fin sc)
    (groups : Fin (GridHosts.tileCount seedAxes depth) ↪ Fin sg)
    (slot boxBase : Fin dir.entries → ℕ) (bank : Fin dir.entries → ℕ → Bool)
    (L : ReportLayout) (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    (D : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    {q : ReportCursor} {wp wd : ℕ}
local notation3 (prettyPrint := false) "payload" => W.retainedBundle (copies:=copies) pos sourceOrder code sites₀ edges₀
  ports₀ channels groups slot boxBase bank
local notation3 (prettyPrint := false) "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation3 (prettyPrint := false) "baseReports" => sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits
local notation3 (prettyPrint := false) "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming
variable {nr cap oldWidth tieWidth : ℕ} {OldAT OldBT TieAT TieBT Z : Type}
variable (oldSchema : FrozenTape.Schema OldAT OldBT) (tieSchema : FrozenTape.Schema TieAT TieBT)
    (input : Fin dir.entries ↪ Fin nr) (known : Fin nr → List (List Factor))
    (oldCap : ∀ j, (oldSchema.tags j).length≤cap) (tieCap : ∀ j, (tieSchema.tags j).length≤cap)
    (privateArgs : Fin (a.cube.cells+1) → E) (reportArgs : Fin (a.cube.cells+1) → List (List E)) (arg : E → ℕ)
    (oldPins : Pins OldAT OldBT oldWidth → Bool) (tiePins : Pins TieAT TieBT tieWidth → Bool)
    (originCell : Fin nr → Fin a.cube.cells) (off box : Fin nr → ℕ) (pointer : Fin dir.entries → Z)
    (base : ℕ → ℕ) (factors : Fin dir.entries → List Factor)
local notation3 (prettyPrint := false) "G" => History.directory oldSchema tieSchema (originalBoxes input known) oldCap tieCap
  privateArgs reportArgs arg oldPins tiePins originCell off box
local notation3 (prettyPrint := false) "T₀" => History.template oldSchema tieSchema (originalBoxes input known) oldCap tieCap privateArgs reportArgs

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 6500 in
/-- Construct the complete issued report input on the actual returned word
arrays and the original labelled seed. Every loaded bundle is the one named
by the original leaf/copy and grammar numbering. -/
noncomputable def SparseEmission.IssuedReportData.fromPinnedSeed {hdr : ℕ}
    (seed : PreparedReportInput pub buf baseReports q dir.description)
    (teamCount : leaves*copies=teams+1) (grammarOrder : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (source : SparseEmission.NativeInputAt a.id U p e patch row dir.description)
    (hf : a.cube.cells+1+(G).words.length+(a.cube.cells+1)≤2^wp)
    (hs : a.cube.cells+1+(Schema.coords ((G).referenceRows pointer).length).length+(a.cube.cells+1)≤2^wd)
    (moved : patch.placed=Terminal.placeAt (signedPlaces (a:=a) (ctl:=ctl) (H:=hdr) G pointer base slot factors R raw hf hs))
    (count : ∀ c : Fin a.cube.cells, ∃ b, (G).reports c.castSucc=DiagonalTallyCellReports.countFields b L.gadgets L.countWidth)
    (bodies : ∀ j, hdr+(boxBody (factors j)).length≤dir.description)
    {group : Fin a.cube.header.d → Fin (teams+1)} {family : TeamRows.Returns (Fin (teams+1)) a.cube w}
    {rowBits : Symbols a.cube.header.d → List Bool}
    {assignment : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) physOwner}
    (observed : ObservedOwned a.cube D group family physOwner rowBits assignment)
    {headerBits : ℕ} (header : Fin dir.entries → Packing.BottomReports.BundleHeader)
    (room : a.OpenRoom frame offsets ctl live ports dir.entries (2^headerBits) w)
    (place : OpenSuffix.Placement (a.openInputs agent.val frame offsets ctl live ports dir.entries headerBits home header)
      a.cube a.before frame (readings (v).owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs agent.val frame offsets ctl live ports dir.entries headerBits home header)
      frame (readings (v).owned.val.2.2) w)
    (ptr : readings orig (frame+92)=ctl)
    (ownerWord : ∀ c : Fin a.cube.cells, readings (v).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      ((physOwner) assignment.1 (label c (chosen a.cube.b a.cube.s assignment.1))).val)
    {I : Type*} [Fintype I] {atSite : I → Fin a.cube.cells} {key : I ↪ ℕ} {widths : I → ℕ} {pins}
    (writer : SlottedWriter a.cube dir pp lp pins pub placed loadBase atSite key widths)
    (wordTeams : dir.teams ≤ 2^w) (wordProcs : dir.processors ≤ 2^w) (wordFields : dir.fields ≤ 2^w)
    (wordLiteral : dir.literal < 2^w) (wordCells : a.cube.cells ≤ 2^w) (wordStride : a.cube.cellStride ≤ 2^w)
    (portWidth : ∀ i, bits (livePorts i)=dir.block)
    (rep : Represents net host aux siteID edgeID portID fieldData x) (ids : ∀ c, (fieldData.cells c).val=c.val)
    (fieldFit : ∀ c, guessedSize net host c+siteSize net host c aux+suppliedSize net host c<2^digits₀)
    (image : Image fieldData (siteID ∘ original) (portID ∘ livePorts ∘ finProdFinEquiv.symm) x origin (readings profile))
    (slots : (privateLayout frame origin a.cube.cables a.cube.cells dir.entries dir.description gap).Image
      (readings profile) dir.entries (readings placed))
    (privateFits : (privateLayout frame origin a.cube.cables a.cube.cells dir.entries dir.description gap).Fits w (readings profile))
    (hdrAt : Header frame origin a.cube.cables a.cube.cells dir.entries (readings profile))
    (reserved : loadBase+7*dir.candidates ≤ origin) (low : origin+5*a.cube.cables ≤ a.cube.header.header)
    (originFit : origin<2^w)
    {before : ℕ → ℕ} (keep : CubeAllocation.HostRetention a.cube frame published before (readings (v).owned.val.2.2))
    (hostMatch : ∀ j, originCell (input j)=host (original j))
    (literal : 0<dir.literal/2) (descriptionFits : dir.description≤dir.literal/2)
    (pairBound : ∀ pair, load (cablePair ord (crossSrc net host) (crossDst net host) label)
      (crossWidth net host ∘ (ord).symm) pair≤a.cube.header.blocks*(a.cube.h*a.cube.b))
    (tailTable : a.before.tailWidths=L.tailWidths)
    (allocation : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl D.1) L baseReports q)
    (extras : patch.extra=seedExtras (visitedReportRows R raw baseRow) q) :
    SparseEmission.IssuedReportData (E:=E) (I:=History.Field cap) (P:=P) (wp:=wp) (wd:=wd)
      (copies:=teams+1) (H:=Branch.pairedTableParameters (k+1) states) (B:=Nat.clog 2 (r*(2*k+1)+1))
      a a.id U p e dir patch row D label recv incoming L home payload eb supply privateWidth digits seed := by
  let delivery := PinStart.returned_issued_delivery a U agent p net host aux siteID edgeID portID
    fieldData x dir origin loadBase gap profile placed writer wordTeams wordProcs wordFields wordLiteral wordCells wordStride
    original livePorts bounds portWidth rep ids fieldFit image slots privateFits hdrAt reserved low originFit keep home header
    ready place D.1 seed allocation (Function.Embedding.refl _) home (fun _ => rfl)
  let locations := Classical.choose delivery.2.2
  have sent := Classical.choose_spec delivery.2.2
  let teams₀ : Fin leaves × Fin copies ↪ Fin (teams+1) := finProdFinEquiv.toEmbedding.trans (finCongr teamCount).toEmbedding
  let marks := W.localSourcePowerSlots (N:=dir.entries) (leaves:=leaves) (copies:=copies) (C:=a.cube.cells)
    (T:=teams+1) (H:=Branch.pairedTableParameters (k+1) states) (l:=L) pos sourceOrder code sites₀ edges₀ ports₀ channels
    groups slot boxBase bank home (fun c => (group (label c D.1)).val) agent.val teams₀
    (ParseTable.numberedLabelEquiv grammarOrder k states).toEmbedding eb supply privateWidth digits
    (fun _ => seed.returnedTape (v).reports) (returnedTapePosition R raw baseReports)
  exact SparseEmission.IssuedReportData.fromHistory a a.id U p e dir patch row D label recv incoming
    L home payload eb supply privateWidth digits seed oldSchema tieSchema input known oldCap tieCap privateArgs reportArgs arg
    oldPins tiePins originCell off box pointer base slot factors source hf hs moved count bodies observed header room place
    ready ptr ownerWord net host edgeID portID ord delivery.1 pp lp delivery.2.1 locations
    (fun j => (sent j).trans (congrArg Fin.val (hostMatch j).symm)) (Function.Embedding.refl _) sent literal
    descriptionFits pairBound tailTable allocation extras marks

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
