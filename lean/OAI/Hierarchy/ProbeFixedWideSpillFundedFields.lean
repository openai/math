import OAI.Hierarchy.ProbeFixedWideSpillFundedChart
import OAI.Hierarchy.TaggedWideSpillPooledLive

namespace OAI
/-! # The actual funded dated turn chart reads the settled role and absolute offset -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart StripDirectory CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen HistoryRoles.RoleProgram WireTelescope ProtocolRAMEmit
open scoped Classical Fin.CommRing
private theorem available_good {n : ℕ} {G : Type} (amount : G → ℕ) (a : SettledMatrix.Source n G Empty)
    (live : 0 < SettledMatrix.Layout.available (fun _ => 0) amount (fun _ => 0) (fun _ => 0) a) :
    ∃ g, a = .inr (.inl g) ∧ 0 < amount g := by
  rcases a with e | g | empty
  · exact (Nat.not_lt_zero _ live).elim
  · exact ⟨g, rfl, live⟩
  · exact empty.elim

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

/-- The prefix observations are supplied by the corrected dated role sheets.
All other words are determined by the original funded turn and its true rank pass. -/
theorem wide_spill_turn_funded_fields
    (heap : (A).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)≤rankFirst)
    (oldStarts : ∀good : Goods h v.W k,0<naturalSpill good→
      ((panel).left.prefix.eval output (((encode) (.inr (.inl good))).val:Word w)).val=
        datedBase (Dated).family ((Dated).bits naturalSpill) ((Dated).num.symm (.inr (.inl good))))
    (newStarts : ∀e:Fin rows,0<routeLoad (mount).ordinary naturalSpill e→
      ((panel).right.prefix.eval output (e.val:Word w)).val=
        datedBase (Dated).edge (routeLoad (mount).ordinary naturalSpill) e)
    (i : ProtocolRAMTurnShelf.Live ((funded).columns ∘ keep)) (side : Bool) :
    let pp:=positions i.val
    let ref:=TurnShelf.refAt (Dated).family (Dated).edge (Dated).routes spines pp side
    (funded).columns (keep i.val) (if side then 1 else 0)=refRole (Dated).routes oldCodes newCodes pp.1 ref ∧
      (funded).columns (keep i.val) (if side then 3 else 2)=
        datedStart (Dated).family (Dated).edge (Dated).routes ((Dated).bits naturalSpill) nativeRank pp.1 ref := by
  intro pp ref
  obtain ⟨pre,rank,rebased⟩:=v.wide_spill_turn_rank_origin (h:=h) (width:=width) (size:=size) (M:=M)
    (π:=π) (raw:=raw) (bits:=bits) (rankFirst:=rankFirst) (j:=j) rankedInput output observed heap (headroom.trans_lt word)
  let depthStock:=fun x:Goods h v.W k=>RouteSettlement.actual (rpage).overflow pre (PurchaseInventory.slot x)
  have eqMass:depthStock=naturalSpill:=funext fun g=>rebased _
  have floors:=(win).bounds
  have enough:=Nat.le_mul_of_pos_right (win).sites (show 0<(win).seats by change 0<slotRoom+(1+9*k);omega)
  have sites : siteLast h D k+1≤2^w:=by change (win).sites≤2^w;obtain ⟨hz,hs,ha,hshelf,hend⟩:=floors;change (win).stop≤turnFirst at oldWindow;omega
  have caps:=v.wide_spill_turn_field_room (h:=h) (width:=width) (size:=size) (M:=M) (π:=π) (raw:=raw)
    (bits:=bits) (issues:=issues) (who:=who) (cj:=cj) (work:=work) (rankFirst:=rankFirst)
    (turnFirst:=turnFirst) (j:=j) oldWindow rankWindow word
  have charged (e : Fin rows):routeLoad (mount).ordinary depthStock e≤counts e:=by
    rw [eqMass]
    exact v.wide_spill_turn_invoice h width size M π raw bits horizon age budget small issues who cj
      rankFirst j rankedInput baseline cost rad paidAge invoiceInput e
  have live:0<((Dated).bits naturalSpill) pp.1:=by
    have pos:=Nat.pos_of_ne_zero i.property
    exact pos.trans_eq (v.wide_spill_turn_funded_widths h width size M π raw bits horizon age budget small operandAge
  issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
  initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
  oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right i.val)
  obtain ⟨good,entry,positive⟩:=available_good naturalSpill ((Dated).num pp.1) live
  have originalWords:=v.wide_spill_turn_original_roles (h:=h) (width:=width) (size:=size) (M:=M) (π:=π)
    (raw:=raw) (bits:=bits) (horizon:=horizon) (age:=age) (budget:=budget) (small:=small) (operandAge:=operandAge)
    (issues:=issues) (card:=card) (who:=who) (cj:=cj) (marks:=marks) (A₀:=A₀) (unique:=unique)
    (datedROM:=datedROM) (terminalROM:=terminalROM) (work:=work) (rankFirst:=rankFirst) (turnFirst:=turnFirst)
    (oldStart:=oldStart) (newStart:=newStart) (leftOnly:=leftOnly) (rightOnly:=rightOnly) (j:=j)
    initial rankedInput output initialLow extended observed replayed within oldWindow rankWindow headroom word sites good
  have code:=ProtocolRAMDateSpillPosition.live_fields v.sampler π tr mount baseChord o (rpage).rankStart slotRoom
    (rpage).overflow pre output rank v.depth marks unique oldQty counts oldPort _ capturedPorts A₀.ident
    (CatalogueRows.Alignment.mounted_chord v.sampler π v.depth marks (P).catalogue order
      (v.wideBoughtOrdinal h width π marks) rawRow A₀ baseChord chk bought)
    (fun _ _ _=>rfl) (activePaid v.sampler counts ports) (panel).data
    (fun n=>((panel).left.prefix.eval output (n:Word w)).val) (fun n=>((panel).right.prefix.eval output (n:Word w)).val)
    charged (fun e=>(caps.2.2.2 e).le) caps.2.2.1 caps.2.1 sites (fun e on whichSide=>DateSpill.printed_fit v.sampler true _ whichSide caps.1)
    i.val (by change 0<(Dated).bits depthStock pp.1;rw [eqMass];exact live) good entry ((encode) (.inr (.inl good))) rfl
    originalWords (by
      change _=datedBase _ ((Dated).bits depthStock) pp.1
      have idx : pp.1=(Dated).num.symm (.inr (.inl good)):=by rw [←entry,Equiv.symm_apply_apply]
      rw [eqMass,idx]
      exact oldStarts good positive)
    (fun e active=>by
      change 0<routeLoad (mount).ordinary depthStock e at active
      change _=datedBase _ (routeLoad (mount).ordinary depthStock) e
      rw [eqMass] at active ⊢;exact newStarts e active) side
  have cols:=v.wide_spill_turn_funded_columns h width size M π raw bits horizon age budget small operandAge
    issues card who cj marks unique A₀ datedROM terminalROM work rankFirst turnFirst oldStart newStart leftOnly rightOnly j
    initial rankedInput output romInput baseline bought cost rad paidAge invoiceInput initialLow rankLow extended observed
    oldQty oldPort capturedPorts retainedROM readOnly replayed within oldWindow rankWindow headroom word left right (keep i.val)
  have startChanged := congrArg (fun amount : Goods h v.W k → ℕ =>
    datedStart (Dated).family (Dated).edge (Dated).routes ((Dated).bits amount) nativeRank pp.1 ref) eqMass
  exact ⟨(congrFun cols (if side then 1 else 0)).trans code.1,
    (congrFun cols (if side then 3 else 2)).trans (code.2.trans startChanged)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
