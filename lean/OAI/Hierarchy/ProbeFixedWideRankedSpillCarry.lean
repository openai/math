import OAI.Hierarchy.ProbeFixedWideSpillRowRead
import OAI.Hierarchy.ProbeFixedWideSpillAccessSource
import OAI.Hierarchy.TaggedWideCalendarControlBounds

namespace OAI
/-! # The spill comparison on a register file emitted by the actual selected RAM execution -/
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
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin (events v.mesh).length → Memory (Native.wordBits h (2^v.W) Native.copies))
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
variable (terminalROM work : ℕ) (j : Fin (events v.mesh).length)
local notation "turnFirst" => (correct).endAt startAt
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
variable (atPrune ranked sch final : Memory (Native.wordBits h (2^v.W) Native.copies))
  (file : v.NativeSpillRegisters h width size M π raw horizon age budget small operandAge issues card who cj marks unique A₀
    ell unitCost first rom oldWork terminalROM work atPrune ranked sch final input)
local notation "naturalSpill" => fun commodity : Goods h v.W k=>
  RouteSettlement.actual (rpage).overflow atPrune (PurchaseInventory.slot commodity)
open Tagged Tagged.WideControlJoin Tagged.WideStack NamedAperture PassiveWindow DatedSpillOffsets
open WireTelescope.PassMatrix HistoryRoles.Terminal RoleProgram
open ThreeFlat Routing
local notation "whole" => sorted v.sampler π v.depth marks ∘ names
local notation "cap" => v.wideNeighborCap width unitCost
local notation "lane" => v.wideNeighborDigits width unitCost
local notation "seats₀" => WordSeats.room (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "oldActive" => (commodityGraph π place).chordWidths naturalSpill
local notation "newActive" => (mount).actual.chordWidths (routeLoad (mount).ordinary naturalSpill)
local notation "activeAt" => fun b : Bool=>cond b newActive oldActive
local notation "workAt" => (correct).spillControlWork startAt
variable {Ex Sel Data : Type} [Fintype Ex] [Fintype Sel] [Fintype Data]
    (gate : Gate) (sameWidth : gate.W=Native.wordBits h (2^v.W) Native.copies) (vertex : Site h (2^v.W) k)
local notation "site" => place vertex
local notation "Pin" => SitePins Ex Sel Data gate
local notation "pt" => (portGraph siteCount).Port site
local notation "ram" => fun i : ℕ=>Fin.cast (congrArg (fun n : ℕ=>2^n) sameWidth.symm) (final i)
include file

/-- The original funded capture, rather than a newly selected transcript, identifies every
control cell and every turn shelf word. Only the two endpoint functions depend on the
local state, so the same native run serves both feed and clipping transitions. -/
theorem wide_native_spill_carry
    (rest : Widths siteCount) (state : ∀b : Bool,State (rest+activeAt b) site)
    (preBound : ∀i,pre j i≤cap) (postBound : ∀i,post j i≤cap)
    (preShape : installedWidths whole (pre j)=rest+oldActive)
    (postShape : installedWidths whole (post j)=rest+newActive)
    (rate : v.sharpPaidUnit≤unitCost) (limitAge : v.wideSpillOverflowHeight≤h)
    (capAge : max (2*uCap) (degs*uCap)≤h) (digitAge : degs*cash≤h)
    (extent : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span stockCap≤first)
    (sitesRoom : siteCount≤2^w) (seatRoom : 2*degs≤2^w) (strideRoom : siteCount*degs≤2^w)
    (floor : v.widthFloor≤width) (dimension : 2*v.keepLimit+2≤2^h) (accepted : chk ((A).endAddress v.mesh)=0)
    (amounts : ∀t i,orig t i≤cash*width)
    (earlyRows : ∀t f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids ranked f)
    (earlyStrides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) ranked)
    (roleFloor : (baseModel).rolesEnd oldWork≤ startAt) (romFloor : rom+siteCount≤ startAt)
    (words : Bool→Fin degs→Fin cap→Pin⊕Bool)
    (inside : ∀f : SiteControls.Field degs,PassMatrix.controlAddress baseModel workAt j site f<gate.u)
    (shelf : ∀t : Fin seats₀,∀c : TurnShelf.Control (TurnShelf.exponent v.wideShelfRoles) lane,
      TurnShelf.addr (panel).base site t (TurnShelf.projection c).1<gate.u)
    (laneSmall : lane≤gate.W+1) (dense : ∀i : Fin gate.u,(gate.addr i).val=i.val)
    (ext : Ex→Bool) (sel : Sel→Bool) (data : Data→Bool)
    :
    let leftParts := PassiveWindow.carried whole (pre j) site preBound
        (PacketNeighbor.localSlot whole (pre j) (named v.sampler π v.depth marks unique names) (shelfSlot v.sampler)
          (named_coordinate v.sampler π v.depth marks unique names) site) preShape;
    let rightParts := PassiveWindow.carried whole (post j) site postBound
        (PacketNeighbor.localSlot whole (post j) (named v.sampler π v.depth marks unique names) (shelfSlot v.sampler)
          (named_coordinate v.sampler π v.depth marks unique names) site) postShape;
    let partsAt := fun b : Bool=>Bool.rec (motive:=fun c=>PassiveWindow.Parts pt (Fin degs) cap
        (fun q=>(rest+activeAt c) q.val.1)) leftParts rightParts b;
    ∀ (_reads : ∀b i q,(partsAt b).owner i=some q→∀u:Fin ((partsAt b).width i),
      Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim data (gate.terminal ram)))) id
        (words b i (u.castLE ((partsAt b).within i)))=((state b) q).val.testBit ((partsAt b).base i+u.val)),
    TypedWiring.value (F:=F) («P»:=Pin) (spillRow (F:=F) (slots:=seats₀) (e:=lane) gate baseModel workAt j site inside
      words laneSmall v.sampler vertex (panel).base (fun a side=>v.wide_shelf_role_fit h a.val side)
      (spillSeat v.sampler vertex)) (Sum.elim ext (Sum.elim sel (Sum.elim data (gate.terminal ram))))=
      LedgerStep.carry ((mount).onlySpill (place).injective baseChord naturalSpill (ProtocolRAMDateSpillRank.spillEnum mount o))
        rest site (state false) (state true) := by
  intro leftParts rightParts partsAt reads
  let evidence:=v.fundedSpillAccess_operands h width size M π raw issues who cj
    marks unique A₀ ell unitCost first rom oldWork terminalROM work atPrune sch file.funds file.origin file.baseline file.bought
    file.cost file.radius file.paidHeight file.stored file.settledLow file.romBelow file.replayed file.terminalFloor
    file.fundedFloor file.oldBefore file.gap file.wordRoom j
  have sections:=correctedContents.frame v h width size M π raw issues marks unique ell unitCost first rom oldWork input
    ranked file.contents (fun a ha=>(file.writtenFrame a ha).symm)
  have pages (t f) : DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids sch f := by
    apply (baseModel).roleFact_local 0 oldWork v.sampler π v.depth marks unique names orig ids rfl
      t f ranked sch _ (earlyRows t f)
    intro a₀ _ highAddress
    have upto:=(WideCPU.role_order baseModel 0 oldWork).upper (finProdFinEquiv (t,f))
    simp only [Equiv.symm_apply_apply] at upto
    exact file.roleFrame a₀ ((highAddress.trans_le upto).trans_le roleFloor)
  have strideNow : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) sch := fun i=>
    (file.roleFrame _ ((Nat.add_lt_add_left i.isLt _).trans_le romFloor)).trans (earlyStrides i)
  have native : first<2^w:=evidence.2.2.2.2.1.trans_lt file.wordRoom
  have salary : stockCap≤2^w := by
    have span:=ProtocolRAMPurchaseSampler.lt_span stockCap
    clear * - span extent native
    omega
  have finance:=(v.wide_funded_extent h width bits).trans horizon
  have current : ∀a<(A).endAddress v.mesh,input j a=chk a:=fun a ha=>
    (file.inputsFrame j a (ha.trans_le ((Nat.le_add_right ..).trans extent))).trans (file.stored a ha)
  have shapes:=v.wide_spill_full_chords h width bits size M π raw first j (input j) unitCost rate limitAge finance floor
    small budget salary file.radius accepted current marks unique issues horizon age amounts
  have wholeBelow (b : Bool) (q₀ : pt) : (rest+activeAt b) q₀.val.1<cap := by
    cases b with
    | false=>
      change (rest+oldActive) q₀.val.1<cap
      rw [←preShape]
      by_cases equation : (correct).attempt j=true
      · simpa only [ite_eq_left equation,wideCorrectedWidths,Fin.cases_succ,ite_eq_left rfl,ite_true] using shapes.2 q₀.val.1
      · simpa only [ite_eq_right equation] using shapes.1 j.castSucc q₀.val.1
    | true=>
      change (rest+newActive) q₀.val.1<cap
      rw [←postShape]
      exact shapes.1 j.succ q₀.val.1
  have bands (b : Bool) (i : Fin degs) : ChordAperture.room (partsAt b) i<2^lane := by
    cases eqn:(partsAt b).owner i with
    | none=>simp [ChordAperture.room,eqn]
    | some q₀=>simpa only [ChordAperture.room,eqn,Option.elim_some,wideNeighborCap] using wholeBelow b q₀
  have decoded:=v.fundedSpillAccess_replay h width size M π raw horizon age budget small operandAge issues card who cj
    marks unique A₀ ell unitCost first rom oldWork terminalROM work atPrune sch file.funds file.origin file.baseline file.bought
    file.cost file.radius file.paidHeight file.stored file.settledLow file.romBelow file.replayed file.terminalFloor
    file.fundedFloor file.oldBefore file.gap file.wordRoom j
  have row := v.wide_spill_row_read (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
    (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (unique:=unique) (A₀:=A₀)
    (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input)
    (terminalROM:=terminalROM) (work:=work) («turnFirst»:=turnFirst) (j:=j)
    (gate:=gate) (sameWidth:=sameWidth) (final:=final) (vertex:=vertex)
    (Ex:=Ex) (Sel:=Sel) (Data:=Data)
    file.funds.before atPrune ranked sch file.funds.romSeed file.baseline file.cost
    sections pages amounts strideNow file.funds.beforeLow file.settledLow file.funds.archive file.inputsFrame
    file.stored (file.origin.2 _ j.isLt) file.funds.amount file.funds.portAt evidence.1
    accepted file.radius file.paidHeight limitAge capAge extent file.replayed evidence.2.2.1 native
    sitesRoom seatRoom strideRoom floor dimension file.bought evidence.2.1 file.romBelow
    (file.terminalFloor.trans evidence.2.2.2.2.1) evidence.2.2.2.1 evidence.2.2.2.2.1
    file.wordRoom evidence.2.2.2.2.2.1 evidence.2.2.2.2.2.2
  apply row rest state preBound postBound preShape postShape rate digitAge words inside shelf laneSmall dense
    ext sel data (fun side port => (wholeBelow side port).le) le_rfl bands
    earlyRows earlyStrides roleFloor romFloor ?_ ?_ reads
  · intro f
    exact file.writtenFrame _ (((correct).calendar_control_addresses startAt j site (deg:=degs) rfl).1 f)
  · intro f a₀
    exact (file.shelf j f a₀).trans (congrArg (fun release : (panel).Inputs turnFirst sch => release.word f a₀) decoded)

/-- Curry the physical placement separately from all original paid register observations. -/
abbrev rankedSpillAt (rate : v.sharpPaidUnit≤unitCost) (limitAge : v.wideSpillOverflowHeight≤h)
    (capAge : max (2*uCap) (degs*uCap)≤h) (digitAge : degs*cash≤h)
    (extent : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span stockCap≤first)
    (sitesRoom : siteCount≤2^w) (seatRoom : 2*degs≤2^w) (strideRoom : siteCount*degs≤2^w)
    (floor : v.widthFloor≤width) (dimension : 2*v.keepLimit+2≤2^h) (accepted : chk ((A).endAddress v.mesh)=0)
    (amounts : ∀t i,orig t i≤cash*width)
    (earlyRows : ∀t f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids ranked f)
    (earlyStrides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) ranked)
    (roleFloor : (baseModel).rolesEnd oldWork≤ startAt) (romFloor : rom+siteCount≤ startAt) :=
  fun {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (board : Gate) (bitWidth : board.W=w)
      (vtx : Site h D k) (pass : Widths siteCount)
      (values : ∀b : Bool,State (pass+activeAt b) (place vtx))
      (low : ∀i,pre j i≤cap) (high : ∀i,post j i≤cap)
      (preEq : installedWidths whole (pre j)=pass+oldActive)
      (postEq : installedWidths whole (post j)=pass+newActive) =>
    v.wide_native_spill_carry (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
      (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
      (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (unique:=unique) (A₀:=A₀)
      (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork)
      (terminalROM:=terminalROM) (work:=work) (j:=j) (input:=input)
      (atPrune:=atPrune) (ranked:=ranked) (sch:=sch) (final:=final)
      (Ex:=X) (Sel:=Y) (Data:=Z) (file:=file)
      (gate:=board) (sameWidth:=bitWidth) (vertex:=vtx) (rest:=pass) (state:=values)
      (preBound:=low) (postBound:=high) (preShape:=preEq) (postShape:=postEq)
      rate limitAge capAge digitAge extent sitesRoom seatRoom strideRoom floor dimension accepted
      amounts earlyRows earlyStrides roleFloor romFloor

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
