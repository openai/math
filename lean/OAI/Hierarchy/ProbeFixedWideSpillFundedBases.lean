import OAI.Hierarchy.ProbeFixedWideSpillFeedSector
import OAI.Hierarchy.ProbeFixedWideSpillFundedChart
import OAI.Hierarchy.ProbeFixedWideSpillOffsetFits
import OAI.Hierarchy.TaggedWideWorkspaceTariff

namespace OAI
/-! # Both measured same-chord prior terms for the funded physical spill circuit -/
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

/-- Complete native old and new offset certificates at one physical date. Corrected
and original role sheets may be transported from their precise earlier program outputs. -/
theorem wide_spill_funded_bases_at_roles (initial rankedInput out : Memory w)
    (baseline : Whole.Reconciliation sink original supply who dur ord ci cj archive)
    (cost : ∀e : Fin rows,paid e+(v.overflowFactor v.keepLimit+fuel v.mesh)*width<2^w)
    (printed : ∀i,(v.wideCorrectedRoleFact h width size M π raw issues marks unique ell unitCost first rom input i).holds out)
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
    (floor : v.widthFloor≤width) (dimension : 2*v.keepLimit+2≤2^h) :
    let spend:=fun c:Gds=>RouteSettlement.actual (region j.val).overflow rankedInput (PurchaseInventory.slot c)
    (∀c : Gds,0<spend c→((panel).left.prefix.eval out (((encode) (.inr (.inl c))).val:Word w)).val=
      datedBase (L₀).family ((L₀).bits spend) ((L₀).num.symm (.inr (.inl c)))) ∧
    ∀e:Fin rows,0<routeLoad (mount).ordinary spend e→((panel).right.prefix.eval out (e.val:Word w)).val=
      datedBase (L₀).edge (routeLoad (mount).ordinary spend) e := by
  intro spend
  have finance:=(v.wide_funded_extent h width bits).trans horizon
  have oldest:=v.wide_replayed_start h width ss
  have preExec : full≤work:=oldest.1.trans readOnly
  have baseLe : work≤rawEnd:=by change work≤work+4*oldRows+4*rows+3*oldRows;omega
  have rawRoom:=room.trans_lt native
  have nRow : oldRows≤2^w:=by change work+4*oldRows+4*rows+3*oldRows<2^w at rawRoom;omega
  have eq:=v.wide_old_rows h width
  have cellRoom : stockCap≤2^w:=by omega
  have fl : (A).endAddress v.mesh≤first:=(Nat.le_add_right ..).trans extent
  have stored (t : Fin last) (x) (h₀:x<(A).endAddress v.mesh) : input t x=chk x :=
    (localFrame t x (h₀.trans_le fl)).trans (invoice x h₀)
  have boundG (t : Fin last) (c:Gds) : clip t c≤lim*width:=
    v.wide_spill_overflow_bound h width bits size M π raw first t (input t) limitAge finance floor small budget cellRoom rad
      accepted (stored t) c
  have boundE (t : Fin last) (e : Fin rows) : routeLoad (mount).ordinary (clip t) e≤v.overflowFactor lim*width:=
    v.wide_spill_route_bound h width bits size M π raw (region t.val) (input t) (boundG t) e
  have income : 2*xx<2^w:=by
    simpa only [Nat.mul_assoc] using v.wide_spill_mul_room h width (2*uCap) ((le_max_left ..).trans capAge) small
  have turnRoom : degs*xx<2^w:=by
    simpa only [Nat.mul_assoc] using v.wide_spill_mul_room h width (degs*uCap) ((le_max_right ..).trans capAge) small
  have wires:=v.wide_spill_chart_sectors_at_roles h width size M π raw issues marks unique ell unitCost first rom oldWork input
    out printed fullPrinted strides nRow sites seats window xx income
    (fun t i=>(amountFits t i).trans (Nat.mul_le_mul_right _ (le_max_left ..)))
    (fun t c=>(boundG t c).trans (Nat.mul_le_mul_right _ ((le_max_left ..).trans (le_max_right ..))))
    (fun t e=>(boundE t e).trans (Nat.mul_le_mul_right _ ((le_max_right ..).trans (le_max_right ..)))) j
  have cashLow:=v.wide_spill_page_floor h width bits first j extent
  have same : clip j=spend:=by
    funext c
    apply congrArg Fin.val
    unfold Bank.read
    exact localFrame j _ ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le cashLow)
  have rb : first≤(region j.val).rankStart:=by change first≤first+_+_+_;omega
  obtain ⟨origin,rank,mem,_⟩:=RankTape.Observation.read (v.wideSpillRanks h width bits first) mount o observed rfl
  have lowNow (x) (hx:x<first) : out x=rankedInput x:=(rank.frame x (hx.trans_le rb)).trans (mem x hx)
  have paidNext (e : Fin rows) : routeLoad (mount).ordinary (clip j) e≤value (j.val+1) (.inl e):=by
    have step : routeLoad (mount).ordinary (clip j) e≤PaidWidths.total (v.wideEventSlices h width bits
        ((events v.mesh).get j)) chk e:=by
      subst M
      exact v.wide_spill_event_le h width bits size π raw first j (input j) paidAge finance small budget (stored j) e
    change _≤v.wirePaidAt h width bits (j.val+1) chk e
    rw [v.wire_paid_next h width bits j chk e]
    omega
  rw [←same]
  constructor
  · intro c yes
    have on:=v.wide_spill_chart_goods_live (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
      (issues:=issues) (marks:=marks) (ell:=ell) (unitCost:=unitCost) (first:=first) (input:=input) j c finance
      ((le_max_right ..).trans age) budget small dimension cellRoom (stored j) yes
    apply v.wide_spill_chart_oldBase (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw) («bits»:=bits)
      (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge) (card:=card)
      (A₀:=A₀) (unique:=unique) (datedROM:=rom) (terminalROM:=terminalROM) (work:=work) (rankFirst:=first) (turnFirst:=turnFirst)
      («oldStart»:=oldStart) («newStart»:=newStart) («leftOnly»:=leftOnly) («rightOnly»:=rightOnly)
      (j:=j) (spill:=clip j) (cap:=xx) (word:=turnRoom)
      (initial:=initial) (out:=out) (initialLow:=initialLow)
      (outLow:=fun x hx=>(lowNow x (hx.trans_le (preExec.trans (baseLe.trans room)))).trans (rankLow x hx))
      (frozen:=fun x hx=>(lowNow x (hx.trans_le room)).trans (rawFrame x hx)) (replayed:=readOnly)
      (room:=room.trans_lt native) (sites:=sites) (whole:=pre j) (seen:=wires.1) (pad:=publicChord h D k)
      (bounded:=fun c=>(boundG j c).trans (Nat.mul_le_mul_right _ ((le_max_left ..).trans (le_max_right ..))))
      (source:=(encode) (.inr (.inl c))) (good:=c) (key:=(encode).symm_apply_apply (.inr (.inl c))) (on:=on)
  · intro e yes
    have positiveNext:=yes.trans_le (paidNext e)
    have finalPaid : 0<counts e:=positiveNext.trans_le
      (v.wide_dated_paid_le h width size M π raw bits horizon age budget small issues who cj baseline cost (j.val+1) e)
    let c:=A₀.ident ⟨e,finalPaid⟩
    have address : ordinal c=e:=(v.wide_dated_original_ordinal h width π marks c).symm.trans (A₀.original _)
    have present : 0<post j ((names).symm (.inl c)):=by
      change 0<value (j.val+1) (embedded (names ((names).symm (.inl c))))
      rw [Equiv.apply_symm_apply]
      change 0<value (j.val+1) (.inl (ordinal c))
      rwa [address]
    apply v.wide_spill_chart_newBase (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw) («bits»:=bits)
      (A₀:=A₀) (unique:=unique) (datedROM:=rom) (terminalROM:=terminalROM) (work:=work) (rankFirst:=first) (turnFirst:=turnFirst)
      («oldStart»:=oldStart) («newStart»:=newStart) («leftOnly»:=leftOnly) («rightOnly»:=rightOnly)
      (j:=j) (spill:=clip j) (cap:=xx) (word:=turnRoom) (out:=out)
      (whole:=post j) (seen:=wires.2) (pad:=publicChord h D k) (e:=e) (bounded:=fun e=>(boundE j e).trans
        (Nat.mul_le_mul_right _ ((le_max_right ..).trans (le_max_right ..))))
      (data:=reported) (positive:=yes) (paidNow:=finalPaid) (on:=present)


/-- The finished program retains all dated role reads. -/
theorem wide_spill_funded_bases (initial rankedInput roleInput out : Memory w)
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
    (floor : v.widthFloor≤width) (dimension : 2*v.keepLimit+2≤2^h) :
    let spend:=fun c:Gds=>RouteSettlement.actual (region j.val).overflow rankedInput (PurchaseInventory.slot c)
    (∀c : Gds,0<spend c→((panel).left.prefix.eval out (((encode) (.inr (.inl c))).val:Word w)).val=
      datedBase (L₀).family ((L₀).bits spend) ((L₀).num.symm (.inr (.inl c)))) ∧
    ∀e:Fin rows,0<routeLoad (mount).ordinary spend e→((panel).right.prefix.eval out (e.val:Word w)).val=
      datedBase (L₀).edge (routeLoad (mount).ordinary spend) e :=
  v.wide_spill_funded_bases_at_roles (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
    (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (unique:=unique) (A₀:=A₀)
    (ell:=ell) (unitCost:=unitCost) (first:=first) (rom:=rom) (oldWork:=oldWork) (input:=input)
    (terminalROM:=terminalROM) (work:=work) (turnFirst:=turnFirst) (j:=j)
    initial rankedInput out baseline cost printed.1 fullPrinted amountFits strides initialLow rankLow rawFrame
    localFrame invoice observed oldQty oldPort reported accepted rad paidAge limitAge capAge extent readOnly room native
    sites seats window floor dimension

end Names
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
