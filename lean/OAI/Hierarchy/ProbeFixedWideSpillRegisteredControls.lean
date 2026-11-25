import OAI.Hierarchy.ProbeFixedWideSpillChartSectors
import OAI.Hierarchy.ProtocolRAMDateSpillControlRoom
import OAI.Hierarchy.ProtocolRAMDateSpillSparseShape
import OAI.Hierarchy.ProbeFixedWideSpillFeedSector

namespace OAI
/-! # Readback of every registered spill overlap word in the original program -/
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open WideCPU StripDirectory PassMatrix
open scoped Classical BigOperators Fin.CommRing
private theorem registeredOffsetRoom {leftBase leftWidth rightBase rightWidth leftLow rightLow limit word : ℕ}
    (side : Bool) (leftTop : leftBase + leftWidth ≤ limit) (rightTop : rightBase + rightWidth ≤ limit)
    (leftSmall : leftLow ≤ limit) (rightSmall : rightLow ≤ limit) (doubleRoom : 2 * limit < word) :
    max (leftBase - leftLow) (rightBase - rightLow) + (if side then rightLow else leftLow) < word := by
  have leftBound := (Nat.sub_le leftBase leftLow).trans ((Nat.le_add_right _ _).trans leftTop)
  have rightBound := (Nat.sub_le rightBase rightLow).trans ((Nat.le_add_right _ _).trans rightTop)
  have selected : (if side then rightLow else leftLow) ≤ limit := by split <;> assumption
  exact (Nat.add_le_add (max_le leftBound rightBound) selected).trans_lt (by simpa only [two_mul] using doubleRoom)

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


variable (size M : ℕ) (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D)
local notation "bits" => v.maxBits
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
variable (horizon : full≤ size) (age : v.wideFundedHeight≤h) (budget : v.keepLimit*width+1≤2^h)
  (small : width≤2^h) (operandAge : v.wideOperandHeight≤h)
  (issues : Attempt→CatalystArchive.Entry num width) (card : recordCount v.mesh issues=cnt)
  (who : Fin (recordCount v.mesh issues)→Fin num) (cj : Columns h D×Fin k→Fin num)
local notation "dur" => debit v.mesh issues
local notation "archive" => result routes (result ((L).scans v.mesh num) (PaidWidths.output (old).width rows
  (TerminalLayout.source page) ss chk))
local notation "closed" => ReserveUse.output original old supply who dur archive
local notation "settled" => (sink).output closed ord ci (fun j=>(cj j).val)
local notation "rawRow" => (sink).terminalRows closed ord ci (fun j=>(cj j).val)
local notation "counts" => fun e : Fin rows=>(rawRow e).width
variable (marks : Marks h v.W k v.wideJobs) (unique : Exclusive marks)
    (A₀ : CatalogueRows.Alignment (P).catalogue v.sampler π v.depth marks M rawRow counts
      ((P).catalogue.original v.sampler π v.depth marks order (v.wideBoughtOrdinal h width π marks)))

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

variable (ell unitCost first rom oldWork : ℕ)
section Names
variable (input : Fin last→Memory w)
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
variable (terminalROM work turnFirst : ℕ) (j : Fin last)
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
open Tagged PassiveWindow SiteControls NamedAperture
local notation "whole" => sorted v.sampler π v.depth marks ∘ names
local notation "cap" => v.wideNeighborCap width unitCost
variable (site : Fin siteCount) (rankedInput roleInput out : Memory w)
local notation "spend" => fun c : Gds=>RouteSettlement.actual (region j.val).overflow rankedInput (PurchaseInventory.slot c)
local notation "oldActive" => (commodityGraph π place).chordWidths spend
local notation "newActive" => (mount).actual.chordWidths (routeLoad (mount).ordinary spend)
local notation "pt" => (portGraph siteCount).Port site
local notation "atSlot" a => PacketNeighbor.localSlot whole a (named v.sampler π v.depth marks unique names)
  (shelfSlot v.sampler) (named_coordinate v.sampler π v.depth marks unique names) site
variable (rest : Widths siteCount) (preBound : ∀i,pre j i≤cap) (postBound : ∀i,post j i≤cap)
    (preShape : installedWidths whole (pre j)=rest+oldActive) (postShape : installedWidths whole (post j)=rest+newActive)
local notation "leftParts" => PassiveWindow.carried whole (pre j) site preBound (atSlot (pre j)) preShape
local notation "rightParts" => PassiveWindow.carried whole (post j) site postBound (atSlot (post j)) postShape
local notation "pass" => fun q : pt=>rest q.val.1
local notation "lBits" => fun q : pt=>oldActive q.val.1
local notation "rBits" => fun q : pt=>newActive q.val.1
local notation "projection" => SiteControls.expected pass lBits rBits leftParts rightParts
include horizon age budget small unique

/-- A true date's gated control scan, including the low spill-only widths and
the active peers at both full chronological sheets. -/
theorem wide_spill_registered_controls
    (printed : v.correctedContents h width size M π raw issues marks unique ell unitCost first rom oldWork input roleInput out)
    (originalFact : ∀t f,DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids roleInput f)
    (strides : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) roleInput)
    (amountFits : ∀t i,orig t i≤cash*width)
    (stored : ∀t x,x<first→input t x=rankedInput x)
    (fees : ∀a<(A).endAddress v.mesh,rankedInput a=chk a)
    (rad : M=v.radius) (rate : v.sharpPaidUnit≤unitCost) (limitAge : v.wideSpillOverflowHeight≤h)
    (accepted : chk ((A).endAddress v.mesh)=0) (extent : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span stockCap≤first)
    (tall : degs*cash≤h) (floor : v.widthFloor≤width)
    (salary : stockCap≤2^w) (rowFit : oldRows≤2^w) (siteFit : siteCount≤2^w)
    (roleFit : 2*degs≤2^w) (spanFit : siteCount*degs≤2^w)
    (roleFloor : (baseModel).rolesEnd oldWork≤ startAt) (romFloor : rom+siteCount≤ startAt) :
    ∀f : SiteControls.Field degs,
      (out (controlAddress baseModel ((correct).spillControlWork startAt) j site f)).val=projection f := by
  obtain ⟨prior,low,roles,_,emitted⟩:=correctedContents.control v h width size M π raw issues marks unique
    ell unitCost first rom oldWork input roleInput printed true j
  have roots (t f) : DatedRoleSheets.roleFact oldRows v.sampler π v.depth marks unique names
      ((baseModel).roleStart oldWork t) (orig t) ids prior f:=by
    apply (baseModel).roleFact_local 0 oldWork v.sampler π v.depth marks unique names orig ids rfl
      t f roleInput prior _ (originalFact t f)
    intro x _ hx
    have ends:=(WideCPU.role_order baseModel 0 oldWork).upper (finProdFinEquiv (t,f))
    simp only [Equiv.symm_apply_apply] at ends
    exact low x ((hx.trans_le ends).trans_le roleFloor)
  have stridesNow : RoleROM.Mounted rom (fun i : Fin siteCount=>i.val*degs) prior:=by
    intro i
    exact (low _ ((Nat.add_lt_add_left i.isLt _).trans_le romFloor)).trans (strides i)
  have capWord:=v.wide_neighbor_double_word h width unitCost tall small
  have countCap : cash*width≤cap:=by
    have strictCap:=v.wide_neighbor_strict width unitCost
    have pos:0<degs:=by unfold HistoryRoles.stride;omega
    exact (Nat.le_mul_of_pos_left _ pos).trans strictCap.le
  have finance:=(v.wide_funded_extent h width bits).trans horizon
  have baseline : (A).endAddress v.mesh≤first:=(Nat.le_add_right ..).trans extent
  have arrived (t : Fin last) (x) (hx:x<(A).endAddress v.mesh) : input t x=chk x:=
    (stored t x (hx.trans_le baseline)).trans (fees x hx)
  have goodsBound (t : Fin last) (i : Gds) : clip t i≤lim*width:=
    v.wide_spill_overflow_bound h width bits size M π raw first t (input t) limitAge finance floor small budget salary rad accepted (arrived t) i
  have paidBound (t : Fin last) (e : Fin rows) : routeLoad (mount).ordinary (clip t) e≤v.overflowFactor lim*width:=
    v.wide_spill_route_bound h width bits size M π raw (region t.val) (input t) (goodsBound t) e
  have margin:=v.wide_spill_unit_room unitCost rate
  have sourceCap (t : Fin last) (i : Gds) : clip t i≤cap:=
    ((goodsBound t i).trans (Nat.mul_le_mul_right _ margin.1)).trans countCap
  have sinkCap (t : Fin last) (e : Fin rows) : routeLoad (mount).ordinary (clip t) e≤cap:=
    ((paidBound t e).trans (Nat.mul_le_mul_right _ margin.2.1)).trans countCap
  have sheets:=v.wide_spill_chart_sectors_at_roles h width size M π raw issues marks unique ell unitCost first rom oldWork input
    prior roles roots stridesNow rowFit siteFit roleFit spanFit cap capWord (fun t i=>(amountFits t i).trans countCap)
      sourceCap sinkCap j
  have beforeCuts:=v.wide_spill_page_floor h width bits first j extent
  have same : clip j=spend:=by
    funext c
    apply congrArg Fin.val
    unfold Bank.read
    exact stored j _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le beforeCuts)
  have oldShape : installedWidths whole (sparseBefore j)=oldActive:=by
    simpa only [←same] using DatedSpillOffsets.old_sparse_shape v.sampler π v.depth marks (P).catalogue order bsize axis (clip j)
  have newShape : installedWidths whole (sparseAfter j)=newActive:=by
    simpa only [←same] using DatedSpillOffsets.new_sparse_shape v.sampler π v.depth marks (P).catalogue order bsize axis chk (clip j)
  have chords:=v.wide_spill_full_chords h width bits size M π raw first j (input j) unitCost rate limitAge finance floor small
    budget salary rad accepted (arrived j) marks unique issues horizon age amountFits
  have leftRoom (p : pt) : (rest+oldActive) p.val.1≤cap:=by
    rw [←preShape]
    change installedWidths whole (if (correct).attempt j then _ else _) p.val.1≤cap
    split
    · exact (chords.2 _).le
    · exact (chords.1 _ _).le
  have rightRoom (p : pt) : (rest+newActive) p.val.1≤cap:=by
    rw [←postShape]
    exact (chords.1 _ _).le
  have lowLeft (p : pt) : oldActive p.val.1≤cap:=(Nat.le_add_left ..).trans (leftRoom p)
  have lowRight (p : pt) : newActive p.val.1≤cap:=(Nat.le_add_left ..).trans (rightRoom p)
  have thinLeft (i) : sparseBefore j i≤cap:=by
    change Sum.elim _ _ (names i)≤cap
    cases names i with
    | inl e=>exact Nat.zero_le _
    | inr y=>cases y with
      | inl c=>exact sourceCap j c
      | inr t=>exact Nat.zero_le _
  have thinRight (i) : sparseAfter j i≤cap:=by
    change Sum.elim _ _ (names i)≤cap
    cases names i with
    | inl e=>exact sinkCap j (ordinal e)
    | inr t=>exact Nat.zero_le _
  have capSmall : cap<2^w:=by omega
  have leftEndpoint:=SectorRead.control_endpoint v.sampler π v.depth marks unique (P).catalogue order bsize axis
    oldRows (oldStart j) (leftOnly j) rom (pre j) (sparseBefore j) prior sheets.1 site preBound thinLeft preShape oldShape capSmall
    (fun p=>(leftRoom p).trans_lt capSmall) (fun p=>(lowLeft p).trans_lt capSmall)
  have rightEndpoint:=SectorRead.control_endpoint v.sampler π v.depth marks unique (P).catalogue order bsize axis
    oldRows (newStart j) (rightOnly j) rom (post j) (sparseAfter j) prior sheets.2 site postBound thinRight postShape newShape capSmall
    (fun p=>(rightRoom p).trans_lt capSmall) (fun p=>(lowRight p).trans_lt capSmall)
  have upLeft:=SiteControls.carried_top whole (pre j) site preBound (atSlot (pre j)) preShape leftRoom
  have upRight:=SiteControls.carried_top whole (post j) site postBound (atSlot (post j)) postShape rightRoom
  intro f
  apply v.wide_spill_control_fields h width ell unitCost bits first rom oldWork startAt j site out prior
    pass lBits rBits leftParts rightParts (emitted site) ?_ f
  apply SiteControls.compile_fields _ _ _ _ _ _ _ _ _ leftEndpoint.1 rightEndpoint.1 leftEndpoint.2 rightEndpoint.2 siteFit capSmall
    (fun i=>(upLeft i).trans_lt capSmall) (fun i=>(upRight i).trans_lt capSmall)
  intro i other side
  have leftTop:=upLeft i
  have rightTop:=upRight other
  have leftLow:=SiteControls.sheet_low_le leftParts lBits lowLeft i
  have rightLow:=SiteControls.sheet_low_le rightParts rBits lowRight other
  change max ((leftParts).base i-((leftParts).view lBits i).low) ((rightParts).base other-((rightParts).view rBits other).low)+
    (if side then ((rightParts).view rBits other).low else ((leftParts).view lBits i).low)<2^w
  exact registeredOffsetRoom side leftTop rightTop leftLow rightLow capWord

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
