import OAI.Hierarchy.ProbeFixedWideSpillRealFields
import OAI.Hierarchy.ProbeFixedWideSpillFundedRoom
import OAI.Hierarchy.ProbeFixedWideSpillRegisteredControls
import OAI.Hierarchy.TaggedWideSpillPooledOutlets
import OAI.Hierarchy.ProbeFixedWideCalendarRow
import OAI.Hierarchy.TaggedWireMountedChord

namespace OAI
/-! # The value of the dated spill row on the funded RAM tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU StripDirectory
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "boards₀" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "E" => v.publicHeader P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger boards₀ v.mesh (P).catalogue (P).routes F A)
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
local notation "L" => ownerLedger boards₀ v.mesh (P).catalogue (P).routes F (TerminalLayout.ownerArea page stride)
local notation "sink" => (P).catalogue.sink r old (TerminalLayout.source page) (TerminalLayout.table page)
  (TerminalLayout.destination page) (sinkBank start cnt r rows)
local notation "C" => v.wideSignedChart h width stock
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
local notation "supply" => fuel v.mesh*width


local notation "own" => TerminalLayout.ownerArea page stride
local notation "incoming" => resolvedStock v.mesh A (P).joint.initial (build F (withPorts boards₀ v.mesh (P).catalogue (P).routes))
local notation "pay" => cashWidthBase F boards₀ v.mesh (P).catalogue (P).routes incoming
local notation "market" => v.catalystMarkets P h width
local notation "o" => wideRouteOrder h D k


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h (2^v.W))
local notation "bits" => v.maxBits
local notation "ss" => v.widePaidSlices h width bits
local notation "seed" => v.wideFundedRaw h width bits raw
local notation "mid" => v.wideSignedMidAt h width size stock M π o seed
local notation "chk" => v.wideSignedCheckoutAt h width size stock M π o seed
local notation "hi" => v.wideRoleStart h width stock ss
local notation "full" => v.wideFundedSize h width bits

local notation "K" => WideMemory.K h v.W
local notation "headerWidth" => WideMemory.H h v.W k v.wideJobs
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "pub" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K (directory).groups headerWidth R
local notation "coreTop" => CoreCatalogue.top h v.W K (directory).groups headerWidth R
local notation "coreHead" => CoreCatalogue.headBase h v.W K (directory).groups headerWidth

local notation "place" => siteNumber h D k
local notation "mount" => (P).catalogue.coreMount π place order chk
local notation "ord" => CoreRoute.enum mount o
local notation "ci" => fun i : Commodity (Fin (2^h)) N k=>PurchaseInventory.slot i
local notation "lw" => v.wideWidthLayout h width ss
variable (horizon : v.wideFundedSize h width v.maxBits ≤ size) (age : v.wideFundedHeight≤h)
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
    (A₀ : WideFundedTurnAlignment v h width size M π raw v.maxBits issues who cj marks)

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

local notation "bsize" => v.wide_dated_bought_rows h width
local notation "axis" => pairKeys (Columns h D) k
local notation "names" => timeRows v.sampler π v.depth marks (P).catalogue order bsize axis
local notation "ordinal" => (P).catalogue.ordinal v.sampler π v.depth marks order bsize
local notation "embedded" => DatedRows.embed v.sampler π v.depth marks (P).catalogue order bsize
local notation "sparse" => sparseKey v.sampler π v.depth marks (P).catalogue order bsize
  (PurchaseInventory.slotEquiv h N k) axis
local notation "partialRow" => DatedRows.lookup v.sampler π v.depth marks (P).catalogue order bsize names
local notation "direction" => DatedRows.inputSide v.sampler π v.depth marks names
local notation "siteCount" => siteLast h D k+1

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option cleanup.letToHave false
variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin (events v.mesh).length→Memory (Native.wordBits h (2^v.W) Native.copies))
local notation "startAt" => v.wideSpillRankEnd h width bits first
local notation "correct" => v.wideSpillDates h width ell unitCost bits first
local notation "baseModel" => v.wideDated h width ell unitCost
local notation "target" => v.wideCorrectedWidths h width size M π raw bits issues first input
local notation "region" => v.wideSpillPage h width bits first
open DatedSpillOffsets
local notation "degs" => HistoryRoles.stride k v.sampler.degree v.wideJobs
local notation "Gds" => Goods h v.W k
local notation "Cts" => Catalysts h v.W k
local notation "Cat" => Catalogue v.sampler π v.depth marks
local notation "clip" => fun j : Fin last=>fun x : Gds=>
  RouteSettlement.actual (region j.val).overflow (input j) (PurchaseInventory.slot x)
local notation "orig" => fun j : Fin (last+1)=>(value j.val ∘ embedded ∘ names)
local notation "post" => fun j : Fin last=>orig j.succ
local notation "pre" => fun j : Fin last=>
  if (correct).attempt j then target 0 j.succ ∘ embedded ∘ names else orig j.castSucc
local notation "sparseBefore" => fun j : Fin last=>((Sum.elim (fun _:Cat=>0) (Sum.elim (clip j) (fun _:Cts=>0))) ∘ names)
local notation "sparseAfter" => fun j : Fin last=>
  ((Sum.elim (fun e:Cat=>routeLoad (mount).ordinary (clip j) (ordinal e)) (fun _:Gds⊕Cts=>0)) ∘ names)
local notation "ids" => fun i=>(sparse (names i)).val
local notation "cert" => SectorRead v.sampler π v.depth marks unique (P).catalogue order bsize axis oldRows

open DateSpill ProtocolRAMDateSpillRank LinearAlgebra.SpectralBooks ChordGraph SiteTensor
local notation "oldStart" => fun j : Fin last=>(correct).preClip oldWork startAt j
local notation "newStart" => fun j : Fin last=>(baseModel).roleStart oldWork j.succ
local notation "leftOnly" => fun j : Fin last=>(correct).dateRole startAt j 1
local notation "rightOnly" => fun j : Fin last=>(correct).dateRole startAt j 2
variable (terminalROM work turnFirst : ℕ) (j : Fin (events v.mesh).length)
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "stock₀" => v.wideTerminalStock h width bits
local notation "rawEnd" => (tr).endAt+3*oldRows
local notation "panel" => v.wideSpillTurnPage h width bits rom terminalROM work first turnFirst oldStart newStart leftOnly rightOnly j
local notation "L₀" => (mount).datedLayout (place).injective (publicChord h D k)
local notation "encode" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "cash" => v.wideHistoryUnit unitCost
local notation "lim" => max v.menu.maximum (v.keepLimit+1)
local notation "uCap" => max cash (max lim (v.overflowFactor lim))
local notation "xx" => uCap*width
local notation "stockCap" => PurchaseInventory.footprint h N k
include horizon age budget small operandAge card A₀ unique

open ProtocolRAMTurnChart ProtocolRAMTurnSnapshot CoreBoard.WordSeats
local notation "baseChord" => publicChord h D k
local notation "rpage" => v.wideSpillPage h width bits first j.val
local notation "Port" => Public v.sampler h v.W k v.wideJobs
local notation "Dated" => (mount).datedLayout (siteNumber h D k).injective baseChord
local notation "keep" => ProtocolRAMDateSpillPosition.chartReal v.sampler π mount baseChord
local notation "positions" => ProtocolRAMDateSpillPosition.positionOrder v.sampler π mount baseChord
local notation "spines" => fun a=>ProtocolRAMDateSpillPosition.sparseSpine v.sampler π mount baseChord ((Dated).num a)
local notation "newCodes" => ProtocolRAMTurnStepOrder.liveCode v.sampler true counts (fun e on side=>
  Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side)))
local notation "oldCodes" => ProtocolRAMDateSpillPosition.originalSpillCodes v.sampler π tr mount baseChord
  (activePaid v.sampler counts ports)
local notation "nativeRank" => (Dated).nativeOrder (ProtocolRAMDateSpillRank.spillEnum mount o)

open Tagged Tagged.WideControlJoin Tagged.WideStack NamedAperture PassiveWindow DatedSpillOffsets
open WireTelescope.PassMatrix HistoryRoles.Terminal RoleProgram
open ThreeFlat Routing
local notation "whole" => sorted v.sampler π v.depth marks ∘ names
local notation "cap" => v.wideNeighborCap width unitCost
local notation "lane" => v.wideNeighborDigits width unitCost
local notation "seats₀" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "workAt" => (correct).spillControlWork startAt
variable {Ex Sel Data : Type} [Fintype Ex] [Fintype Sel] [Fintype Data]
    (gate : Gate) (sameWidth : gate.W=Native.wordBits h (2^v.W) Native.copies) (final : Memory (Native.wordBits h (2^v.W) Native.copies)) (vertex : Site h (2^v.W) k)
local notation "site" => place vertex
local notation "Pin" => SitePins Ex Sel Data gate
local notation "pt" => (portGraph siteCount).Port site
local notation "ram" => fun i : ℕ=>Fin.cast (congrArg (fun n : ℕ=>2^n) sameWidth.symm) (final i)
local notation "part" a hb hs => PassiveWindow.carried whole a site hb (PacketNeighbor.localSlot whole a
    (named v.sampler π v.depth marks unique names) (shelfSlot v.sampler)
    (named_coordinate v.sampler π v.depth marks unique names) site) hs

omit horizon age budget small operandAge card A₀ unique in
private theorem entry_cast {W₀ W₁ n₀ s₀ c₀ : ℕ} (eq : W₀=W₁) (col : Fin n₀→Fin 7→ℕ)
    (put : ProtocolRAMTurnShelf.Live col ↪ Fin s₀×Fin c₀) (f : Fin 5) (a : Fin s₀×Fin c₀) :
    Fin.cast (congrArg (fun n : ℕ=>2^n) eq) (ProtocolRAMTurnShelf.entry (W:=W₀) col put f a)=
      ProtocolRAMTurnShelf.entry (W:=W₁) col put f a := by subst W₁;rfl

attribute [local irreducible] Nat.pow Native.wordBits

/-- Evaluation on the actual mounted shelf and the two dated packed role sheets.
The external bit condition uses the original local seat indices on each whole chord. -/
theorem wide_spill_row_read (initial rankedInput roleInput out romInput : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (printed : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input roleInput out)
    (fullPrinted : ∀t f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids out f)
    (amountFits : ∀t i,orig t i≤cash*width)
    (strides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) out)
    (initialLow : ∀a<full,initial a=settled a) (rankLow : ∀a<full,rankedInput a=settled a)
    (rawFrame : ∀x<rawEnd,rankedInput x=(tr).extendedState stock₀ initial x)
    (localFrame : ∀t x,x<first→input t x=rankedInput x)
    (invoice : ∀a<(A).endAddress v.mesh,rankedInput a=chk a)
    (observed : RankTape.Observation (v.wideSpillRanks h width bits first) mount o j.val rankedInput out)
    (oldQty : Fin oldRows→ℕ)
    (oldPort : ∀i,0<oldQty i→Bool→Public v.sampler h v.W k v.wideJobs)
    (reported : (tr).LiveReads v.sampler oldQty counts oldPort (fun e on side=>.inl (ports e on side)) out)
    (accepted : chk ((A).endAddress v.mesh)=0) (rad : M=v.radius)
    (paidAge : v.wideSpillPaidHeight≤h) (limitAge : v.wideSpillOverflowHeight≤h)
    (capAge : max (2*uCap) (degs*uCap)≤h)
    (extent : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span stockCap≤first)
    (readOnly : v.wideReplayedTurnBase h width ss≤work)
    (room : rawEnd≤first) (native : first<2^w)
    (sites : siteCount≤2^w) (seats : 2*degs≤2^w) (window : siteCount*degs≤2^w)
    (floor : v.widthFloor≤width) (dimension : 2*v.keepLimit+2≤2^h)
    (bought : ∀boughtIndex : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex boughtIndex))
      ((P).catalogue.bought.view chk (boughtIndex.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex boughtIndex).val))
    (retainedROM : ∀a,terminalROM≤a→a<v.wideTerminalROMEnd h width bits terminalROM work→
      out a=v.wideTerminalWords h width bits terminalROM work romInput a)
    (romBefore : v.wideTerminalROMEnd h width bits terminalROM work≤work)
    (oldWindow : v.wideTerminalWorkEnd h width bits work≤turnFirst)
    (rankWindow : (rpage).offsetsStart≤turnFirst) (headroom : first≤turnFirst) (word : turnFirst<2^w)
    (left : (panel).left.prefix.Fits w turnFirst) (right : (panel).right.prefix.Fits w turnFirst) :
    let spillPublisher := wide_spill_turn_funded_chart v h width size M π raw bits horizon age budget small operandAge
      issues card who cj marks unique A₀ rom terminalROM work first turnFirst oldStart newStart leftOnly rightOnly j
      initial rankedInput out romInput baseline bought cost rad paidAge invoice initialLow rankLow rawFrame observed
      oldQty oldPort reported retainedROM romBefore readOnly room oldWindow rankWindow headroom word left right;
    let sourceAmounts := fun commodity : Goods h v.W k => RouteSettlement.actual (rpage).overflow rankedInput (PurchaseInventory.slot commodity);
    let sourceWidths := (commodityGraph π place).chordWidths sourceAmounts;
    let targetWidths := (mount).actual.chordWidths (routeLoad (mount).ordinary sourceAmounts);
    let activeWidths := fun b : Bool => cond b targetWidths sourceWidths;
    ∀ (rest : Widths siteCount) (state : ∀b : Bool,State (rest+activeWidths b) site)
      (preBound : ∀i,pre j i≤cap) (postBound : ∀i,post j i≤cap)
      (preShape : installedWidths whole (pre j)=rest+sourceWidths)
      (postShape : installedWidths whole (post j)=rest+targetWidths),
      let leftParts := PassiveWindow.carried whole (pre j) site preBound (PacketNeighbor.localSlot whole (pre j)
        (named v.sampler π v.depth marks unique names) (shelfSlot v.sampler)
        (named_coordinate v.sampler π v.depth marks unique names) site) preShape;
      let rightParts := PassiveWindow.carried whole (post j) site postBound (PacketNeighbor.localSlot whole (post j)
        (named v.sampler π v.depth marks unique names) (shelfSlot v.sampler)
        (named_coordinate v.sampler π v.depth marks unique names) site) postShape;
      let partsAt := fun b : Bool => Bool.rec (motive:=fun c=>PassiveWindow.Parts pt (Fin degs) cap
        (fun q=>(rest+activeWidths c) q.val.1)) leftParts rightParts b;
      ∀ (_rate : v.sharpPaidUnit≤unitCost)
      (_digitAge : HistoryRoles.stride k v.sampler.degree v.wideJobs*cash≤h)
      (words : Bool→Fin degs→Fin cap→Pin⊕Bool)
      (inside : ∀f : SiteControls.Field degs,PassMatrix.controlAddress baseModel workAt j site f<gate.u)
      (_shelf : ∀t : Fin seats₀,∀c : TurnShelf.Control (TurnShelf.exponent v.wideShelfRoles) lane,
        TurnShelf.addr (panel).base site t (TurnShelf.projection c).1<gate.u)
      (laneSmall : lane≤gate.W+1) (_dense : ∀i : Fin gate.u,(gate.addr i).val=i.val)
      (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
      (_wholeFit : ∀b (q : pt),(rest+activeWidths b) q.val.1≤cap)
      (_columns : cap≤2^lane) (_roomAt : ∀b q,ChordAperture.room (partsAt b) q<2^lane)
      (_earlyRows : ∀t f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
        ((baseModel).roleStart oldWork t) (orig t) ids roleInput f)
      (_earlyStrides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) roleInput)
      (_roleFloor : (baseModel).rolesEnd oldWork≤ startAt) (_romFloor : rom+siteCount≤ startAt)
      (_preserved : ∀f : SiteControls.Field degs,final (PassMatrix.controlAddress baseModel workAt j site f)=
        out (PassMatrix.controlAddress baseModel workAt j site f))
      (_mounted : ∀f a,final (TurnShelf.addr (panel).base a.1 a.2 f)=spillPublisher.word f a)
      (_reads : ∀b i q,(partsAt b).owner i=some q→∀u:Fin ((partsAt b).width i),
        Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim data (gate.terminal ram)))) id
          (words b i (u.castLE ((partsAt b).within i)))=((state b) q).val.testBit ((partsAt b).base i+u.val)),
        TypedWiring.value (spillRow (F:=F) (slots:=seats₀) (e:=lane) gate baseModel workAt j site inside
          words laneSmall v.sampler vertex (panel).base (fun a side=>v.wide_shelf_role_fit h a.val side)
          (spillSeat v.sampler vertex)) (Sum.elim ext (Sum.elim sel (Sum.elim data (gate.terminal ram))))=
          LedgerStep.carry ((mount).onlySpill (place).injective baseChord sourceAmounts (ProtocolRAMDateSpillRank.spillEnum mount o))
            rest site (state false) (state true) := by
  intro spillPublisher sourceAmounts sourceWidths targetWidths activeWidths rest state preBound postBound
    preShape postShape leftParts rightParts partsAt rate digitAge words inside shelf laneSmall dense ext sel data wholeFit
    columns roomAt earlyRows earlyStrides roleFloor romFloor preserved mounted reads
  let project := SiteControls.expected (fun q : pt=>rest q.val.1) (fun q : pt=>sourceWidths q.val.1)
    (fun q : pt=>targetWidths q.val.1) leftParts rightParts
  let sparseRows := spillPublisher.columns ∘ keep
  let placement := (ProtocolRAMTurnShelf.restrictedLive spillPublisher.columns keep).trans spillPublisher.put
  have boardRoom : oldRows≤2^w:=by
    have b:=room.trans_lt native
    change work+4*oldRows+4*rows+3*oldRows<2^w at b
    omega
  have stockRoom : stockCap≤2^w:=by
    have b:=v.wide_old_rows h width
    omega
  have controls (f : SiteControls.Field degs) :
      (final (PassMatrix.controlAddress baseModel workAt j site f)).val=project f := by
    rw [preserved]
    exact v.wide_spill_registered_controls (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
      (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (issues:=issues) (marks:=marks)
      (unique:=unique) (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork)
      (input:=input) (j:=j) («site»:=site) (rankedInput:=rankedInput) (roleInput:=roleInput) (out:=out) (rest:=rest)
      (preBound:=preBound) (postBound:=postBound) (preShape:=preShape) (postShape:=postShape)
      printed earlyRows earlyStrides amountFits localFrame invoice rad rate limitAge accepted extent
      digitAge floor stockRoom boardRoom sites seats window roleFloor romFloor f
  have real := v.wide_spill_real_fields (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
    (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (unique:=unique) (A₀:=A₀)
    (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input)
    (terminalROM:=terminalROM) (work:=work) (turnFirst:=turnFirst) (j:=j)
    initial rankedInput roleInput out romInput baseline cost printed fullPrinted amountFits strides initialLow rankLow
    rawFrame localFrame invoice observed oldQty oldPort reported accepted rad paidAge limitAge capAge extent readOnly
    room native sites seats window floor dimension bought retainedROM romBefore oldWindow rankWindow headroom word left right
  have bases:=v.wide_spill_funded_bases (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
    (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (unique:=unique) (A₀:=A₀)
    (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input)
    (terminalROM:=terminalROM) (work:=work) (turnFirst:=turnFirst) (j:=j)
    initial rankedInput roleInput out baseline cost printed fullPrinted amountFits strides initialLow rankLow rawFrame
    localFrame invoice observed oldQty oldPort reported accepted rad paidAge limitAge capAge extent readOnly room native
    sites seats window floor dimension
  have charges:=v.wide_spill_turn_funded_fits h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ rom terminalROM work first turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput out romInput baseline bought cost rad paidAge invoice initialLow rankLow rawFrame observed
    oldQty oldPort reported retainedROM romBefore readOnly room oldWindow rankWindow headroom word left right
    extent bases.1 bases.2 unitCost rate limitAge digitAge floor accepted
  have auth:=v.wide_spill_turn_funded_chart_word h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ rom terminalROM work first turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput out romInput baseline bought cost rad paidAge invoice initialLow rankLow rawFrame observed
    oldQty oldPort reported retainedROM romBefore readOnly room oldWindow rankWindow headroom word left right
  have weights:=v.wide_spill_turn_funded_widths h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ rom terminalROM work first turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput out romInput baseline bought cost rad paidAge invoice initialLow rankLow rawFrame observed
    oldQty oldPort reported retainedROM romBefore readOnly room oldWindow rankWindow headroom word left right
  have charged (e : Fin rows):routeLoad (mount).ordinary sourceAmounts e≤counts e:=
    v.wide_spill_turn_invoice h width size M π raw bits horizon age budget small issues who cj
      first j rankedInput baseline cost rad paidAge invoice e
  refine spillRow_carry gate baseModel workAt j site inside words laneSmall v.sampler vertex (panel).base
    (fun a side=>v.wide_shelf_role_fit h a.val side) (spillSeat v.sampler vertex) mount (place).injective baseChord
    sourceAmounts (ProtocolRAMDateSpillRank.spillEnum mount o) rest state partsAt ram ext sel data dense wholeFit
    columns roomAt ?_ ?_ ?_ ?_ ?_ reads spines positions sparseRows placement weights (fun u=>Fin.ext (auth.2 u))
    oldCodes newCodes (fun u b=>(real.2 u b).1) (fun u b=>(real.2 u b).2) ?_
    (by rw [sameWidth];exact charges.1) charges.2.1 charges.2.2 shelf ?_ ?_
  · intro b i q
    cases b
    · exact controls (.inl (false, .inl (i,q)))
    · exact controls (.inl (true, .inl (i,q)))
  · intro b i side
    cases b
    · exact controls (.inl (false, .inr (.inl (i,side))))
    · exact controls (.inl (true, .inr (.inl (i,side))))
  · intro b q
    cases b
    · exact controls (.inl (false, .inr (.inr q)))
    · exact controls (.inl (true, .inr (.inr q)))
  · intro i q
    exact controls (.inr ((i,q),0))
  · intro i q b
    cases b
    · exact controls (.inr ((i,q),1))
    · exact controls (.inr ((i,q),2))
  · intro f a
    exact (congrArg (Fin.cast (congrArg (fun bitsCount : ℕ => 2^bitsCount) sameWidth.symm))
      ((mounted f a).trans (auth.1 f a))).trans (entry_cast sameWidth.symm sparseRows placement f a)
  · exact DatedSpillOffsets.original_outlet v.sampler π v.depth marks unique names vertex (pre j)
      preBound preShape tr mount baseChord sourceAmounts (activePaid v.sampler counts ports) real.1.1
  · intro sourceIndex edgeAt digit side location
    have aligned (edge : {e : Fin rows // 0 < counts e}) :
        filledChord (mount).actual baseChord edge.val =
          sorted v.sampler π v.depth marks (.inl (A₀.ident edge)) :=
      CatalogueRows.Alignment.mounted_chord v.sampler π v.depth marks (P).catalogue order
        (v.wideBoughtOrdinal h width π marks) rawRow A₀ baseChord chk bought edge
    have atRole (edge : Fin rows) (positive : 0 < routeLoad (mount).ordinary sourceAmounts edge) :
        0 < post j ((names).symm (.inl (A₀.ident ⟨edge, positive.trans_le (charged edge)⟩))) :=
      (real.1.2 edge positive).choose_spec
    let identify : {e : Fin rows // 0 < counts e} → Catalogue v.sampler π v.depth marks :=
      fun edge => A₀.ident edge
    have atDestination := DatedSpillOffsets.paid_outlet
      (h:=h) (W:=v.W) (k:=k) (attempts:=v.wideJobs) (n:=Fintype.card (HistoryRoles.Source v.sampler π v.depth marks))
      (total:=rest+targetWidths) («cap»:=cap) («r»:=rows+ProtocolRAMDateSpillRank.coreCount o)
      v.sampler π v.depth marks unique names vertex (post j) postBound postShape tr mount baseChord
      sourceAmounts nativeRank (fun edge : Fin rows => counts edge) charged identify aligned atRole
      sourceIndex edgeAt digit side location
    exact atDestination

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
