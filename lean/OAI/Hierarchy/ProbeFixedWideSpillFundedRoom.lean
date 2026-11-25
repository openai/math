import OAI.Hierarchy.ProbeFixedWideSpillFundedFields
import OAI.Hierarchy.ProbeFixedWideSpillFieldRoom
import OAI.Hierarchy.TaggedWideTerminalSiteTariff

namespace OAI
/-! # Field and decoder widths of the actual funded calendar spill program -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option cleanup.letToHave false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^h



open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "order" => v.wideOrder h width
local notation "sheet" => v.wideSignedPage h width


local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "original" => TerminalLayout.reserve start cnt page
local notation "L" => ownerLedger s v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "geometrySource" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) geometrySource v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts s v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F s v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W)) (bits : ℕ)
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups H R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups H R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups H

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
local notation "last" => (events v.mesh).length

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (card : recordCount v.mesh issues = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k))
  (cj : Columns h (2^v.W)×Fin k→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who cj marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)

local notation "shape" => RoleRoom.shape («R»:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "z" => shape
local notation "ports" => livePort v.sampler (P).catalogue π marks unique order (v.wideBoughtOrdinal h width π marks) A₀
local notation "oldRows" => Fintype.card (Old h v.W k rows)
local notation "value" => v.wideDatedValue h width bits mid chk issues
local notation "tb" => v.wideTerminalBoard h width bits 0

include horizon age budget small operandAge card


open DateSpill ProtocolRAMDateSpillRank ProtocolRAMTurnChart ProtocolRAMTurnSnapshot
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open CoreBoard.WordSeats
include marks unique A₀
variable (datedROM terminalROM work rankFirst turnFirst : ℕ)
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ) (j : Fin (events v.mesh).length)
local notation "panel" => v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
  oldStart newStart leftOnly rightOnly j
local notation "ranker" => v.wideSpillRanks h width bits rankFirst
local notation "rpage" => v.wideSpillPage h width bits rankFirst j.val
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "stk" => v.wideTerminalStock h width bits
local notation "extent₀" => (tr).endAt+3*oldRows
local notation "slotRoom" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "RawOld" => ProtocolRAMTurnGeometry.Source rows h D k
local notation "decode" => (ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
local notation "encode" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "chart" => captured (panel).data

local notation "win" => v.wideTurnWindow h width bits work
local notation "T" => v.wideTerminal h width bits terminalROM work
local notation "baseChord" => publicChord h D k
local notation "Port" => Public v.sampler h v.W k v.wideJobs


open private sparseBaseline sparseBought sparseSettled sparseCounts sparseMount sparseCheckout from
  OAI.Hierarchy.ProbeFixedWideSpillFundedChart
variable (initial rankedInput output romInput : Memory (Native.wordBits h (2^v.W) Native.copies))
    (baseline : sparseBaseline v h width size M π raw bits issues who cj)
    (bought : sparseBought v h width size M π raw bits issues who cj)
    (cost : ∀e : Fin (v.widePlacement h width).catalogue.rows,
      PaidWidths.total (v.widePaidSlices h width bits) (sparseCheckout v h width size M π raw bits) e +(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^(Native.wordBits h (2^v.W) Native.copies))
    (rad : M=v.radius) (paidAge : v.wideSpillPaidHeight≤h)
    (invoiceInput : ∀a<(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh,rankedInput a=sparseCheckout v h width size M π raw bits a)
    (initialLow : ∀a<v.wideFundedSize h width bits,initial a=sparseSettled v h width size M π raw bits issues who cj a) (rankLow : ∀a<v.wideFundedSize h width bits,rankedInput a=sparseSettled v h width size M π raw bits issues who cj a)
    (extended : ∀a<((v.wideTerminalBoard h width bits work).endAt + 3*Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows)),rankedInput a=(v.wideTerminalBoard h width bits work).extendedState (v.wideTerminalStock h width bits) initial a)
    (observed : RankTape.Observation (v.wideSpillRanks h width bits rankFirst)
      (sparseMount v h width size M π raw bits) (wideRouteOrder h (2^v.W) k) j.val rankedInput output)
    (oldQty : Fin (Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows))→ℕ) (oldPort : ∀i,0<oldQty i→Bool→Public v.sampler h v.W k v.wideJobs)
    (capturedPorts : (v.wideTerminalBoard h width bits work).LiveReads v.sampler oldQty
      (sparseCounts v h width size M π raw bits issues who cj) oldPort
      (fun e on side=>Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side))) output)
    (retainedROM : ∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM work→
      output a=v.wideTerminalWords h width bits terminalROM work romInput a)
    (readOnly : v.wideTerminalROMEnd h width bits terminalROM work≤work)
    (replayed : v.wideReplayedTurnBase h width (v.widePaidSlices h width bits)≤work) (within : ((v.wideTerminalBoard h width bits work).endAt + 3*Fintype.card (Old h v.W k (v.widePlacement h width).catalogue.rows))≤rankFirst)
    (oldWindow : v.wideTerminalWorkEnd h width bits work≤turnFirst)
    (rankWindow : (v.wideSpillPage h width bits rankFirst j.val).offsetsStart≤turnFirst) (headroom : rankFirst≤turnFirst) (word : turnFirst<2^(Native.wordBits h (2^v.W) Native.copies))
    (left : (v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
      oldStart newStart leftOnly rightOnly j).left.prefix.Fits (Native.wordBits h (2^v.W) Native.copies) turnFirst) (right : (v.wideSpillTurnPage h width bits datedROM terminalROM work rankFirst turnFirst
      oldStart newStart leftOnly rightOnly j).right.prefix.Fits (Native.wordBits h (2^v.W) Native.copies) turnFirst)
include baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed capturedPorts
  retainedROM readOnly replayed within oldWindow rankWindow headroom word left right


local notation "funded" => wide_spill_turn_funded_chart v h width size M π raw bits horizon age budget small operandAge
  issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
  initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
  oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right

local notation "naturalSpill" => fun g:Goods h v.W k=>RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot g)
local notation "Dated" => (mount).datedLayout (siteNumber h D k).injective baseChord
local notation "keep" => ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
local notation "positions" => ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord
local notation "spines" => fun a=>ProtocolRAMDateSpillPosition.sparseSpine v.sampler π mount baseChord ((Dated).num a)
local notation "newCodes" => ProtocolRAMTurnStepOrder.liveCode v.sampler true counts (fun e on side=>
  Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side)))
local notation "oldCodes" => ProtocolRAMDateSpillPosition.originalSpillCodes v.sampler π tr mount baseChord
  (activePaid v.sampler counts ports)
local notation "nativeRank" => (Dated).nativeOrder (ProtocolRAMDateSpillRank.spillEnum mount o)

theorem wide_spill_turn_funded_fits
    (heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)≤rankFirst)
    (oldStarts : ∀g:Goods h v.W k,0<naturalSpill g→
      ((panel).left.prefix.eval output (((encode) (.inr (.inl g))).val:Word w)).val=
        datedBase (Dated).family ((Dated).bits naturalSpill) ((Dated).num.symm (.inr (.inl g))))
    (newStarts : ∀e:Fin rows,0<routeLoad (mount).ordinary naturalSpill e→
      ((panel).right.prefix.eval output (e.val:Word w)).val=
        datedBase (Dated).edge (routeLoad (mount).ordinary naturalSpill) e)
    (unitCost : ℕ) (rate : v.sharpPaidUnit≤unitCost) (overflowAge : v.wideSpillOverflowHeight≤h)
    (digitAge : HistoryRoles.stride k v.sampler.degree v.wideJobs*v.wideHistoryUnit unitCost≤h)
    (widthFloor : v.widthFloor≤width) (accepted : chk ((A).endAddress v.mesh)=0) :
    let col:=(funded).columns ∘ keep
    let p₀:=TurnShelf.exponent v.wideShelfRoles
    let e:=v.wideNeighborDigits width unitCost
    (∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^w) ∧
    (∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 1 else 0)<2^p₀) ∧
    ∀u : ProtocolRAMTurnShelf.Live col,∀b : Bool,col u.val (if b then 3 else 2)+col u.val 4≤2^e := by
  have fields:=v.wide_spill_turn_funded_fields h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
    oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right heap oldStarts newStarts
  have sizes:=v.wide_spill_turn_funded_widths h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
    oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right
  have caps:=v.wide_spill_turn_field_room (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (bits:=bits) (issues:=issues) (who:=who) (cj:=cj) (work:=work) (rankFirst:=rankFirst)
    (turnFirst:=turnFirst) (j:=j) oldWindow rankWindow word
  have cells : PurchaseInventory.footprint h N k≤2^w := by
    have padded:=ProtocolRAMPurchaseSampler.lt_span (PurchaseInventory.footprint h N k)
    omega
  have finance:=(v.wide_funded_extent h width bits).trans horizon
  have apertures:=v.wide_spill_chord_caps h width bits size M π raw rankFirst j rankedInput unitCost rate
    overflowAge finance widthFloor small budget cells rad accepted invoiceInput marks unique
  have printedCode (kind : Bool) (arr : Bool→Port) (b : Bool) :
      ProtocolRAMTurnOperands.printed v.sampler kind arr b false<
        min (2^TurnShelf.exponent v.wideShelfRoles) (2^w) := by
    apply lt_min
    · exact v.wide_shelf_role_fit h _ kind
    · exact DateSpill.printed_fit v.sampler kind arr b caps.1
  apply dated_fields_fit (Dated).family (Dated).edge (Dated).routes ((Dated).bits naturalSpill) nativeRank
    (TurnShelf.exponent v.wideShelfRoles) (v.wideNeighborDigits width unitCost) w
    ((funded).columns ∘ keep) (fun u=>(positions u).1)
    (fun u side=>TurnShelf.refAt (Dated).family (Dated).edge (Dated).routes spines (positions u) side)
    oldCodes newCodes sizes (fun u b=>(fields u b).1) (fun u b=>(fields u b).2) apertures.1 apertures.2
  · intro i side
    exact printedCode false _ side
  · intro i side
    unfold ProtocolRAMTurnStepOrder.liveCode
    split
    · exact printedCode true _ side
    · exact lt_min (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  · exact v.wide_neighbor_word h width unitCost digitAge small
  · intro i
    change SettledMatrix.Layout.available (fun _:Fin rows=>0) naturalSpill (fun _:Empty=>0) (fun _=>0)
      ((Dated).num i)<2^w
    cases key:(Dated).num i with
    | inl e=>exact Nat.two_pow_pos _
    | inr x=>cases x with
      | inl g=>exact (Bank.read _ _ _).isLt
      | inr v=>exact v.elim


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
