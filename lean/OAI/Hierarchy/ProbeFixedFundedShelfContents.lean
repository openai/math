import OAI.Hierarchy.ProbeFixedWideTerminalFloors
import OAI.Hierarchy.ProbeFixedFundedTerminalRun
import OAI.Hierarchy.ProtocolRAMFundedTurnFields
import OAI.Hierarchy.ProtocolRAMPaidCanonicalTurns
import OAI.Hierarchy.ProtocolRAMTurnReportedCodes
import OAI.Hierarchy.TaggedWireShelfContents

namespace OAI
/-! # All five observed words of the actual funded terminal execution -/

set_option quotPrecheck false

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
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
local notation "last" => (events v.mesh).length
local notation "g" => CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W) (directory).groups
  (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
local notation "routes" => CoreRoute.stages old (routeBanks start cnt r) g v.sampler h v.W k v.wideJobs
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

variable (horizon : v.wideFundedSize h width bits ≤ size) (age : v.wideFundedHeight≤h)
  (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry (Fintype.card (Columns h (2^v.W))*k) width)
  (card : recordCount v.mesh issues = rowOnlyCount v.mesh (declaredRows v.mesh
    (ownerLedger (v.nativeBoards (v.widePlacement h width) h width) v.mesh
      (v.widePlacement h width).catalogue (v.widePlacement h width).routes F
      (v.privateArena (v.widePlacement h width) h width))))
  (who : Fin (recordCount v.mesh issues)→Fin (Fintype.card (Columns h (2^v.W))*k))
local notation "cj" => pairKeys (Columns h D) k
local notation "dur" => CatalystArchive.debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : WideFundedTurnAlignment v h width size M π raw bits issues who
      (CatalystArchive.pairKeys (Columns h (2^v.W)) k) marks)

local notation "paid" => PaidWidths.total ss chk
local notation "goods" => fun i : Commodity (Fin (2^h)) N k=>RouteSettlement.actual (old).stock closed (ci i)
local notation "held" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).reserved closed (cj j).val
local notation "taken" => fun j : Columns h D×Fin k=>RouteSettlement.actual (old).used closed (cj j).val
local notation "term" => (mount).actual.chordWidths paid+(commodityGraph π place).chordWidths goods+
  (catalystGraph place).chordWidths (fun j=>held j-taken j)


local notation "paidAtLast" => (lw).bank last
variable (rom work : ℕ)
local notation "T" => v.wideTerminal h width bits rom work
local notation "tr" => v.wideTerminalBoard h width bits work
local notation "lo" => v.wideTerminalRankStart h width bits work
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder rows h D k).symm
local notation "oIdx" => ProtocolRAMTurnGeometry.sourceOrder rows h D k
local notation "pad" => publicChord h D k
local notation "port" => Public v.sampler h v.W k v.wideJobs


open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMTurnChart ProtocolRAMTurnSnapshot ProtocolRAMPaidTurnPlacement
local notation "matrix" => (mount).matrixLayout (place).injective pad
local notation "account" => SettledMatrix.Layout.bits paid goods held taken
local notation "modes" => WordSeats.fixedRoom (k:=k) (attempts:=v.wideJobs) v.sampler
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "geo" => ProtocolRAMTurnGeometry.header o modes names
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len
  (fun a=>ProtocolRAMTurnEdges.visit mount (place).injective pad (names a))
local notation "n" => rows+r
local notation "phase" => Canonical.posn mount (place).injective pad
local notation "spine" => Canonical.spines mount (place).injective pad
local notation "win" => v.wideTurnWindow h width bits work
local notation "newPort" => CatalogueRows.Alignment.originalPort v.sampler π v.depth marks unique (P).catalogue order
  (v.wideBoughtOrdinal h width π marks) rawRow A₀

/-- The literal paid/source and reported/output labels used by the physical finish gate
refer to the same original paid row, in either printed orientation. -/
theorem wide_funded_shelf_endpoints
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    (∀e : {e // 0<Z.fixed e},let ends:=actualEnds v.sampler π v.depth marks (Z.fixedOriginal v.depth marks A₀.ident e)
      ((rawRow e.val).endpoint=(HistoryRoles.name ends.1).val ∧ (rawRow e.val).opposite=(HistoryRoles.name ends.2).val) ∨
      ((rawRow e.val).endpoint=(HistoryRoles.name ends.2).val ∧ (rawRow e.val).opposite=(HistoryRoles.name ends.1).val)) ∧
    ∀e : Fin rows, ∀on : 0<(rawRow e).width,∀side,
      HistoryRoles.name (HistoryRoles.site v.sampler (newPort ⟨e,on⟩ side))=(rowGraph (matrix).edge).vertex e side := by
  intro Z
  constructor
  · exact fun e=>A₀.joins ⟨e.val,Z.fixed_live_width e.val e.property⟩
  · intro e on side
    exact ProtocolRAMPaidTurnPlacement.paid_vertex v.sampler π v.depth marks unique (P).catalogue order
      (v.wideBoughtOrdinal h width π marks) rawRow A₀ (matrix).edge
      (CatalogueRows.Alignment.mounted_chord v.sampler π v.depth marks (P).catalogue order
        (v.wideBoughtOrdinal h width π marks) rawRow A₀ pad chk read) ⟨e,on⟩ side

private theorem shelf_dictionary_congr {α β γ : Type*} (readValue : α → β → γ)
    {left oldTable : α} {right newTable : β} (sameLeft : left=oldTable) (sameRight : right=newTable) :
    readValue left right = readValue oldTable newTable := by
  cases sameLeft
  cases sameRight
  rfl

private theorem shelf_rank_room (priorCells ranks edgeCount padding : ℕ) :
    ranks ≤ priorCells+ranks+edgeCount+3+padding := by omega

private theorem shelf_sites_room (windowLayout : ProtocolRAMTurnWindow.Layout) (wide : ℕ)
    (slotPositive : 0<windowLayout.seats) (limit : windowLayout.stop≤wide) : windowLayout.sites≤wide := by
  obtain ⟨_,_,_,cells,finish⟩ := windowLayout.bounds
  have nonempty := Nat.le_mul_of_pos_right windowLayout.sites slotPositive
  omega

include operandAge card
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
attribute [local irreducible] PaidWidths.output ReserveUse.output CoreRoute.stages Sink.output Sink.terminalRows
  wideFundedSize wideSignedCheckoutAt wideSignedMidAt

/-- The native terminal is executed on the real funded cut and its public fixed role
and offset words describe precisely the report's incoming and outgoing sockets. -/
theorem wide_funded_shelf_archive (initial m : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (charged : ∀j : Fin num,RouteSettlement.actual (old).used closed j.val=
      usedAt (CatalystArchive.site v.mesh issues) dur j ∧ RouteSettlement.actual (old).reserved closed j.val=supply)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (keep : ∀x,x<full→m x=settled x)
    (lastRead : ∀i : Fin rows,(m ((paidAtLast).base+i.val)).val=paid i)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (afterReplay : v.wideReplayedTurnBase h width ss≤work)
    (room : v.wideTerminalWorkEnd h width bits work≤2^w)
    («public» : ∀x,rom≤x→x<v.wideTerminalROMEnd h width bits rom work→
      m x=v.wideTerminalWords h width bits rom work initial x)
    (romBefore : v.wideTerminalROMEnd h width bits rom work≤work) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    let oldPort:=Terminal.ports v.sampler π v.depth marks unique Z.fixed Z.stock Z.reserved Z.used
      (Z.fixedOriginal v.depth marks A₀.ident)
    let oldCode:=fun i side=>if on:0<SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used i
      then labelled v.sampler false (oldPort ⟨(i,side),on⟩) else 0
    let newCode:=fun i side=>if on:0<(rawRow i).width then labelled v.sampler true (newPort ⟨i,on⟩ side) else 0
    ∃out : Memory w,((T).code w paidAtLast).Exec m out ((T).ticks paidAtLast) ∧ (∀a<work,out a=m a) ∧
      (∀a<(tr).endAt+3*(tr).old,out a=(tr).extendedState (T).stock m a) ∧
      (tr).LiveReads v.sampler account counts
        (fun i _ side=>publicRoleFor v.sampler π (Z.beforePay v.depth marks unique A₀.ident) (names i) side)
        (fun e on side=>Sum.inl (HistoryRoles.paid v.sampler π v.depth marks unique (A₀.ident ⟨e,on⟩,side))) out ∧
      Z.ShelfContents (T).seats (T).turns (T).base out oldCode newCode := by
  intro Z oldPort oldCode newCode
  let S:=v.sampler
  let before (i : Fin (tr).old) (_ : 0<account i) side : port :=
    publicRoleFor S π (Z.beforePay v.depth marks unique A₀.ident) (names i) side
  let after (e : Fin rows) (on : 0<(rawRow e).width) side : port :=
    .inl (HistoryRoles.paid S π v.depth marks unique (A₀.ident ⟨e,on⟩,side))
  let native:=v.wide_funded_terminal_at h width size M π raw bits horizon age budget small operandAge issues card who
    marks unique A₀ rom work initial m baseline charged read keep lastRead cost afterReplay room «public» romBefore true
  obtain ⟨post,kept,out,exec,stored,frame,windowFrame,auth,offsets,keys,rawFrame,_⟩:=native
  have observed : (tr).LiveReads S account (fun e=>(rawRow e).width) before after post:=auth
  let chart:=captured (T).columns post
  let vals:=ProtocolRAMTurnSnapshot.values (T).walk post
  let recordAt:=ProtocolRAMTurnChart.record geo chart visit
  let col:=ProtocolRAMTurnInstalled.columns recordAt vals
  have aligns (i : {i : Fin rows // 0<(rawRow i).width}) :
      filledChord (mount).actual pad i.val=HistoryRoles.sorted S π v.depth marks (.inl (A₀.ident i)) :=
    CatalogueRows.Alignment.mounted_chord S π v.depth marks (P).catalogue order
      (v.wideBoughtOrdinal h width π marks) rawRow A₀ pad chk read i
  have alignFixed:=Z.fixedOriginal_position v.depth marks A₀.ident aligns
  have oldAt (i : Fin rows) : account (oIdx (.inl i))=Z.fixed i := by
    exact congrArg (SettledMatrix.Layout.available paid goods held taken)
      ((oIdx).symm_apply_apply (.inl i))
  let castID : {i : Fin rows // 0<account (oIdx (.inl i))} ↪ {i : Fin rows // 0<Z.fixed i} :=
    ⟨fun i=>⟨i.val,i.property.trans_eq (oldAt i.val)⟩,fun _ _ eq=>
      Subtype.ext (congrArg (fun e : {e : Fin rows // 0<Z.fixed e}=>e.val) eq)⟩
  let id:=castID.trans (Z.fixedOriginal v.depth marks A₀.ident)
  let put:=ProtocolRAMPaidTurnPlacement.chartPut S π v.depth marks unique mount pad
    (fun i : Fin rows=>account (oIdx (.inl i))) id names col kept
  have sourceWidth (i : Fin (tr).old) : chart.width i.val=account i :=
    ProtocolRAMTurnSnapshot.width_at S tr observed (T).columns.site (T).columns.half i
  have widths:=Canonical.widths mount (place).injective pad o modes chart vals account sourceWidth
  obtain ⟨workStart,roleEnd,windowEnd,floorStop,originalFits,edgeFits⟩:=v.wide_terminal_role_floors h width bits work room
  have rawWords (a : ℕ) (ha : a<(tr).endAt+3*(tr).old) : out a=(tr).extendedState (T).stock m a :=
    (windowFrame a (ha.trans_le (roleEnd.trans windowEnd))).trans (rawFrame a (ha.trans_le roleEnd))
  have afterLive:=Board.LiveReads.frame (S:=S) (b:=tr) observed (v.wideTurnWindow h width bits work).floor (roleEnd.trans windowEnd)
    originalFits edgeFits windowFrame
  refine ⟨out,exec,frame,rawWords,afterLive,spine,phase,col,put,stored,widths,?_,?_⟩
  · exact Canonical.put_site S π v.depth marks unique mount pad _ id
      (fun e=>alignFixed (castID e)) col kept
  intro u side
  let i:=(phase u.val).1
  let j:=(phase u.val).2
  have on : 0<account i := (Nat.pos_of_ne_zero u.property).trans_eq (widths u.val)
  have retain : ProtocolRAMLiveTurnOrder.retain Z.fixed (names i) := by
    let z:=names i
    have live : 0<SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used z:=on
    change ProtocolRAMLiveTurnOrder.retain Z.fixed z
    rcases z with e|a|c
    · exact live
    · trivial
    · trivial
  have endpoints (b : Bool) : HistoryRoles.name (HistoryRoles.site S (before i on b))=
      originalEnd S π mount pad (names i) b :=
    original_side S π v.depth marks unique mount pad Z.fixed (Z.fixedOriginal v.depth marks A₀.ident)
      (Z.beforePay v.depth marks unique A₀.ident) alignFixed (Z.beforePay_live v.depth marks unique A₀.ident)
      (names i) retain b
  have high : (win).stop≤2^w:=room
  have floor : (win).floor=lo+2^ProtocolRAMPackedRanked.groupBits n+2^ProtocolRAMPackedRanked.groupBits n+
      2*n+3*n+4*n+rows+3+2^ProtocolRAMPackedRanked.groupBits (4*n):=rfl
  have floorRoom : (win).floor≤2^w := floorStop.trans high
  have wordRoom : 4*n≤2^w := by
    apply Nat.le_trans _ floorRoom
    rw [floor]
    exact shelf_rank_room _ _ _ _
  have slotPositive : 0<(win).seats := by
    change 0< modes+(1+9*k)
    omega
  have sitesRoom : (T).sites≤2^w := shelf_sites_room (win) _ slotPositive high
  have here:=Canonical.reverse_captured S π mount pad tr observed (T).columns.site (T).columns.half
    i on (names i) endpoints sitesRoom
  obtain ⟨item,origin,length,reverse,pos,site⟩:=Canonical.fields mount (place).injective pad o modes chart u.val here
  have countRoles : 2*modes≤2^w := by
    have span:=ProtocolRAMSupergroupDirectory.slotFits (2*modes)
    have endROM : (win).halfBase rom+ProtocolRAMSupergroupDirectory.span (2*modes)≤work:=romBefore
    have workBound : work≤2^w :=
      workStart.trans ((Nat.le_add_right _ _).trans (roleEnd.trans (windowEnd.trans floorRoom)))
    exact span.le.trans ((Nat.le_add_left _ _).trans (endROM.trans workBound))
  have fitLabel (a : port) (age : Bool) : labelled S age a<2^w := by
    have rank : HistoryRoles.code S a< modes:=HistoryRoles.code_bound S a
    cases age <;> simp only [HistoryRoles.RoleProgram.labelled,Bool.toNat_false,Bool.toNat_true] <;> omega
  have fitPrint (a : Bool→port) (age b : Bool) :
      ProtocolRAMTurnOperands.printed S age a b false<2^w := fitLabel _ _
  have newTail (e : Fin rows) (live : 0<(rawRow e).width) :
      ProtocolRAMTurnOperands.printed S true (after e live) false true=((matrix).edge e).1.1.val :=
    (paid_printed_ends S π v.depth marks unique mount pad e (A₀.ident ⟨e,live⟩)
      (after e live) (aligns ⟨e,live⟩) (fun _=>rfl)).1
  have fits (e : Fin rows) : Z.widthAt e<2^w := by
    change ((sink).terminalRows closed ord ci (fun j=>(cj j).val) e).width<2^w
    unfold Sink.terminalRows
    exact ((RouteSettlement.fields (sink).banks (sink).geometry 4).eval
      (RouteSettlement.output (sink).banks (sink).source closed ord ci (fun j=>(cj j).val)) (e.val:Word w)).isLt
  have reported:=Z.receipt.native_width (place).injective pad
  have actualRank:=v.wide_funded_terminal_widths h width size M π raw bits horizon age budget small issues who
    marks A₀ baseline read cost
  rw [actualRank] at offsets
  have fields:=v.wide_turn_field_pair h width bits rom work mount Z.fixed Z.stock Z.reserved Z.used Z.widthAt
    before after post (recordAt u.val) i on (spine i) j item origin length reverse pos site observed
    keys offsets wordRoom sitesRoom (fun b=>fitPrint _ _ b) (fun e live b=>fitPrint _ _ b)
    (Z.named_live_uses_positive (names i) on) newTail
    (fun q=>(congrFun reported (((matrix).routes i).get q)).trans_lt (fits _)) side
  have oldEq : ProtocolRAMTurnStepOrder.liveCode v.sampler false
      (SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used) before=oldCode :=
    funext fun t=>funext fun b=>Z.input_socket_code v.depth marks unique A₀.ident t b
  have newEq : ProtocolRAMTurnStepOrder.liveCode v.sampler true Z.widthAt after=newCode :=
    funext fun t=>funext fun b=>ProtocolRAMPaidTurnPlacement.paid_code S π v.depth marks unique (P).catalogue
      order (v.wideBoughtOrdinal h width π marks) rawRow A₀ t b
  let shelfRef := TurnShelf.refAt (matrix).family (matrix).edge (matrix).routes spine (phase u.val) side
  let readRole (leftTable : Fin (tr).old → Bool → ℕ) (rightTable : Fin rows → Bool → ℕ) :=
    WireTelescope.refRole (matrix).routes leftTable rightTable i shelfRef
  have codeAt : readRole (ProtocolRAMTurnStepOrder.liveCode v.sampler false
      (SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used) before)
      (ProtocolRAMTurnStepOrder.liveCode v.sampler true Z.widthAt after) = readRole oldCode newCode :=
    shelf_dictionary_congr readRole oldEq newEq
  exact ⟨fields.1.trans codeAt,fields.2⟩

/-- The shelf coefficient alone, forgetting the retained eleven-column native role board. -/
theorem wide_funded_shelf_contents (initial m : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (charged : ∀j : Fin num,RouteSettlement.actual (old).used closed j.val=
      usedAt (CatalystArchive.site v.mesh issues) dur j ∧ RouteSettlement.actual (old).reserved closed j.val=supply)
    (read : ∀j : Fin (P).catalogue.boughtRows,Reads (rawRow ((P).catalogue.boughtIndex j))
      ((P).catalogue.bought.view chk (j.val:Word w)) ((P).catalogue.idBase+((P).catalogue.boughtIndex j).val))
    (keep : ∀x,x<full→m x=settled x)
    (lastRead : ∀i : Fin rows,(m ((paidAtLast).base+i.val)).val=paid i)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (afterReplay : v.wideReplayedTurnBase h width ss≤work)
    (room : v.wideTerminalWorkEnd h width bits work≤2^w)
    («public» : ∀x,rom≤x→x<v.wideTerminalROMEnd h width bits rom work→
      m x=v.wideTerminalWords h width bits rom work initial x)
    (romBefore : v.wideTerminalROMEnd h width bits rom work≤work) :
    let Z:=v.wide_report_at h width size M π raw bits horizon age budget small issues who cj marks A₀ baseline read cost
    let oldPort:=Terminal.ports v.sampler π v.depth marks unique Z.fixed Z.stock Z.reserved Z.used
      (Z.fixedOriginal v.depth marks A₀.ident)
    let oldCode:=fun i side=>if on:0<SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used i
      then labelled v.sampler false (oldPort ⟨(i,side),on⟩) else 0
    let newCode:=fun i side=>if on:0<(rawRow i).width then labelled v.sampler true (newPort ⟨i,on⟩ side) else 0
    ∃out : Memory w,((T).code w paidAtLast).Exec m out ((T).ticks paidAtLast) ∧ (∀a<work,out a=m a) ∧
      Z.ShelfContents (T).seats (T).turns (T).base out oldCode newCode := by
  obtain ⟨out,ran,kept,_,_,shelf⟩:=v.wide_funded_shelf_archive h width size M π raw bits horizon age budget small
    operandAge issues card who marks unique A₀ rom work initial m baseline charged read keep lastRead cost
    afterReplay room «public» romBefore
  exact ⟨out,ran,kept,shelf⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
