import OAI.Computability.BorderVNP.DiagonalIssuedArgumentWindow
import OAI.Computability.BorderVNP.DiagonalNativeInputAt
import OAI.Computability.BorderVNP.DiagonalIssuedSourceGeometry

/-! # Constructing the concrete signed report frame from the issued packet and its original history -/

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
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) {agent : Fin (teams+1)} (p : (U agent).Prefix id)

local notation3 (prettyPrint := false) "pub" => (U agent).pub
local notation3 (prettyPrint := false) "frame" => ((U agent).pub 0).val
local notation3 (prettyPrint := false) "mac" => CompactMachine.install SparseExterior.driver n (U agent).routines
local notation3 (prettyPrint := false) "v" => PinStart.visits id U p
local notation3 (prettyPrint := false) "orig" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "buf" => (v).controls.val.2.2
local notation3 (prettyPrint := false) "stages" => (argumentVisitsEquiv pub mac (v).reports.val.2.1 orig).symm (v).arguments
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame frame (readings orig)

variable {fit : (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).Fits w
      (readings (PinStart.visits id U p).reports.val.2.2)}
    {cells : a.fragments.cells=(FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2)).cells}
    (e : SparseEmission a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
      (PinStart.visits id U p).reports.val.2.2 fit cells)
    {offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool} (dir : Packing.Directory.Layout)
set_option quotPrecheck false
local notation "R" => a.controlRows agent.val frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) (Fin dir.entries) (a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a (FragmentRows.Layout.fromFrame ((U agent).pub 0).val (readings (PinStart.visits id U p).reports.val.2.2))
        (PinStart.visits id U p).reports.val.2.2 data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=agent.val) («frame»:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

variable {E I P A : Type} [Fintype P] [Fintype A] {wp wd copies H B : ℕ}
    (D : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ)
    {J : ℕ} (L : ReportLayout) (home : Fin J → Fin a.cube.cells) (payload : Fin J → ReportBundle)
    (eb supply privateWidth : ℕ → ℕ) (digits : ℕ → Fin L.gadgets → Fin L.countWidth → Bool)
    {q : ReportCursor}
local notation "baseRow" => sourceCell L home payload eb supply privateWidth digits
local notation "baseReports" => sourceCells L home payload agent.val ((R).owner raw) eb supply privateWidth digits
variable (seed : PreparedReportInput ((U agent).pub) (PinStart.visits id U p).controls.val.2.2
    (sourceCells L home payload agent.val ((a.controlRows agent.val ((U agent).pub 0).val offsets ctl live ports).owner
      (readings e.output)) eb supply privateWidth digits) q dir.description)
local notation "tape" => seed.returnedTape (v).reports
local notation "position" => returnedTapePosition R raw baseReports
local notation "atReported" => fun c : ℕ => (baseRow c).withTape tape (position c)
local notation "sample" => fun c : Fin a.cube.cells => (atReported) c.val
local notation "actualReports" => ((assignedReportReturnEquiv seed mac (v).controls.val.2.1).symm (v).reports).val
local notation "physOwner" => greedyOwner teams a.cube.b a.cube.s label recv incoming


open CellPacketGeometry.History CellPacketGeometry.History.Native Packing.Inherited FrozenTape

variable {nr cap oldWidth tieWidth : ℕ} {OldAT OldBT TieAT TieBT Z : Type}
variable (oldSchema : FrozenTape.Schema OldAT OldBT) (tieSchema : FrozenTape.Schema TieAT TieBT)
    (input : Fin dir.entries ↪ Fin nr) (known : Fin nr → List (List Factor))
    (oldCap : ∀ j, (oldSchema.tags j).length≤cap) (tieCap : ∀ j, (tieSchema.tags j).length≤cap)
    (privateArgs : Fin (a.cube.cells+1) → E) (reportArgs : Fin (a.cube.cells+1) → List (List E)) (arg : E → ℕ)
    (oldPins : Pins OldAT OldBT oldWidth → Bool) (tiePins : Pins TieAT TieBT tieWidth → Bool)
    (originCell : Fin nr → Fin a.cube.cells) (off box : Fin nr → ℕ) (pointer : Fin dir.entries → Z)
    (base : ℕ → ℕ) (slot : Fin dir.entries → ℕ) (factors : Fin dir.entries → List Factor)
local notation3 (prettyPrint := false) "G" => History.directory oldSchema tieSchema (originalBoxes input known) oldCap tieCap
  privateArgs reportArgs arg oldPins tiePins originCell off box
local notation3 (prettyPrint := false) "T₀" => History.template oldSchema tieSchema (originalBoxes input known) oldCap tieCap privateArgs reportArgs

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 6000 in
/-- Assemble the source record on the already obtained typed call. Header
and geometry bounds are derived from the original live sorted packet, and
report fields are taken from the actually prepared owned-cell scanner. -/
noncomputable def SparseEmission.IssuedReportData.fromHistory {hdr : ℕ}
    (source : SparseEmission.NativeInputAt id U p e patch row dir.description)
    (hf : a.cube.cells+1+(G).words.length+(a.cube.cells+1)≤2^wp)
    (hs : a.cube.cells+1+(Schema.coords ((G).referenceRows pointer).length).length+(a.cube.cells+1)≤2^wd)
    (moved : patch.placed=Terminal.placeAt (signedPlaces (a:=a) (ctl:=ctl) (H:=hdr) G pointer base slot factors R raw hf hs))
    (count : ∀ c : Fin a.cube.cells, ∃ b, (G).reports c.castSucc=DiagonalTallyCellReports.countFields b L.gadgets L.countWidth)
    (bodies : ∀ j, hdr+(boxBody (factors j)).length≤dir.description)
    {group : Fin a.cube.header.d → Fin (teams+1)} {family : TeamRows.Returns (Fin (teams+1)) a.cube w}
    {rowBits : Symbols a.cube.header.d → List Bool}
    {assignment : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) physOwner}
    (observed : ObservedOwned a.cube D group family physOwner rowBits assignment)
    {headerBits : ℕ} (header : Fin J → Packing.BottomReports.BundleHeader)
    (room : a.OpenRoom frame offsets ctl live ports J (2^headerBits) w)
    (place : OpenSuffix.Placement (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
      a.cube a.before frame (readings (v).owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs agent.val frame offsets ctl live ports J headerBits home header)
      frame (readings (v).owned.val.2.2) w)
    (ptr : readings orig (frame+92)=ctl)
    (ownerWord : ∀ c : Fin a.cube.cells, readings (v).owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      ((physOwner) assignment.1 (label c (chosen a.cube.b a.cube.s assignment.1))).val)
    {z ne np nc : ℕ} {bits : P → ℕ} (N : Network z P bits) (host : N.Site → Fin a.cube.cells)
    (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np) (ord : N.CrossingEdge host ≃ Fin nc)
    (cables : CableRows N host edge port (f).host (readings orig))
    (pp lp : ℕ → ℕ × ℕ)
    (physicalRows : (List.range (f).count).map ((f).row (readings orig))=dir.directory pp lp)
    (located : RowLocations (dir.directory pp lp) (Fin.val : Fin a.cube.cells → ℕ) recv incoming)
    (originalSent : ∀ j, (pp j.val).1=(originCell (input j)).val)
    (bundleEntry : Fin J ↪ Fin dir.entries) (sentTo : ∀ j, (pp (bundleEntry j).val).1=(home j).val)
    (literal : 0<dir.literal/2) (descriptionFits : dir.description≤dir.literal/2)
    (pairBound : ∀ pair, load (cablePair ord (crossSrc N host) (crossDst N host) label)
      (crossWidth N host ∘ ord.symm) pair ≤ a.cube.header.blocks*(a.cube.h*a.cube.b))
    (tailTable : a.before.tailWidths=L.tailWidths)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter frame ctl D.1) L baseReports q)
    (emitExtras : patch.extra=seedExtras (visitedReportRows R raw baseRow) q)
    (sourceMarks : ((c : {c : Fin a.cube.cells // (group (label c D.1)).val=agent.val}) × UsePositions (((sample) c.val).bundles)) ↪
      Diagonal.CellEntries.PowerSlot (Fin copies) (Fin H) B) :
    SparseEmission.IssuedReportData (E:=E) (I:=History.Field cap) (P:=P) (wp:=wp) (wd:=wd) (copies:=copies) (H:=H) (B:=B)
      a id U p e dir patch row D label recv incoming L home payload eb supply privateWidth digits seed := by
  let table : LiveWords.Template E (History.Field cap) (Fin dir.entries) (History.roster nr oldSchema tieSchema).length (a.cube.cells+1) := T₀
  let owner := cellOf oldSchema tieSchema oldPins tiePins originCell
  let fields := fun i => scalarArgs (cap:=cap) oldSchema tieSchema oldPins tiePins off box ((History.roster nr oldSchema tieSchema).get i)
  have geometry : Nonempty (dir.OriginalBoxRows pp (fun c : Fin a.cube.cells => patch.placed c.val)) ∧
      TypedBatch.SourceFootprint (fun c : Fin (a.cube.cells+1) => patch.placed c.val) (table.directory owner arg fields) ∧
      (a.cube.cells+1)+table.atoms.length+(a.cube.cells+1)≤2^wp ∧
      (a.cube.cells+1)+(Schema.coords table.chunkLabels.length).length+(a.cube.cells+1)≤2^wd ∧
      (∀ c : Fin a.cube.cells, (patch.placed c.val).reports.length=L.gadgets) ∧
      (∀ c : Fin a.cube.cells, ∀ ds ∈ (patch.placed c.val).reports, ds.length=L.countWidth) ∧
      (∀ c : ℕ, ∀ j, (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length≤dir.description) :=
    issuedSourceGeometry (a:=a) (wp:=wp) (wd:=wd) (ctrl:=ctl) (hdr:=hdr) dir oldSchema tieSchema
      input known oldCap tieCap privateArgs reportArgs arg oldPins tiePins originCell off box pointer base slot factors R raw
      hf hs patch.placed moved pp originalSent L count bodies
  clear_value table owner fields
  let boxes := geometry.1.some
  have shape := geometry.2.1
  have pubCap := geometry.2.2.1
  have descCap := geometry.2.2.2.1
  have counts := geometry.2.2.2.2.1
  have width := geometry.2.2.2.2.2.1
  have extent := geometry.2.2.2.2.2.2
  exact ⟨source.native,source.roster,source.owned,source.tasks,source.facts,source.address,
    group,family,rowBits,assignment,observed,headerBits,header,room,place,ready,ptr,ownerWord,
    z,(History.roster nr oldSchema tieSchema).length,ne,np,nc,bits,N,host,edge,port,ord,cables,pp,lp,
    physicalRows,located,boxes,bundleEntry,sentTo,literal,descriptionFits,pairBound,
    table,owner,arg,fields,shape,pubCap,descCap,counts,width,(fun c _ _ j => extent c j),tailTable,alloc,emitExtras,sourceMarks⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
