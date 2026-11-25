import OAI.Hierarchy.ProtocolRAMCatalystStripRun
import OAI.Hierarchy.ProtocolRAMCatalystDateHeader

namespace OAI
/-! # Settlement with the literal subdivision columns and signed header at every date -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe CoreRoute CatalystArchive CatalogueRows ProbeStage CoreBoard
open StripDirectory ColumnWires StockCommit
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical

variable {z W k q depth K R H scale payload K₁ jobs size phases X Y steps : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "w" => Native.wordBits z D Native.copies
local notation "r" => Fintype.card (Slots z D k)
local notation "num" => Fintype.card (CoreBoard.Columns z D)*k

variable (F : Type) [_root_.Field F] [Nonempty (Fin k)] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z (2^W) k q depth) (c : Mesh)
  (cat : CatalogueRows.Board) (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (A ownerArea : Arena)
  (initialStock feedWidth cap : ℕ) (finish : ℝ) (fees : PhasePrice) (banks : RouteSettlement.Banks)
  (src table dst : ℕ) (owners : Bank) (flag paymentSource : ℕ) (slices : List PaidWidths.Slice)
  (a : ReserveUse.Archive) (p : Recipes) (o : Orders z (2^W) k)
  (order : Fin R≃Edges s.sampler z (2^W) k) (M : ℕ) (groups : Fin g.oldGroups≃AllGroups z (2^W))
local notation "attempts" => (c.inject+c.cool)*c.outerFuel
variable (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) g.height)
  (socket : BoughtSockets.Directory ((c.inject+c.cool)*c.outerFuel)) (π : Equiv.Perm (Fin (2^z))) (place : Site z (2^W) k→Fin K₁)
  (B : Mount (S:=s.sampler) π place cat.rows)
local notation "rows" => withPorts s c cat g
local notation "sink" => cat.sink r banks src table dst owners
local notation "C" => chart F c A initialStock feedWidth cap rows finish fees cat r banks src table dst owners
local notation "L" => ownerLedger s c cat g F ownerArea
local notation "incoming" => resolvedStock c A initialStock (build F rows)
local notation "pay" => cashWidthBase F s c cat g incoming
local notation "decl" => declaredRows c L
local notation "idSrc" => rowOnly c decl (ownerArea.base c)
local notation "amtSrc" => rowOnly c decl pay
local notation "f" => formats F c A initialStock rows
local notation "label" => (fun t=> (f t).labelSource sink cat.idBase (header F rows t).fieldTerm (id F rows cat t))
local notation "pair" => pairKeys (CoreBoard.Columns z D) k
local notation "ci" => (PurchaseInventory.slot : Commodity (Fin (2^z)) N k→ℕ)
local notation "cj" => (fun t : CoreBoard.Columns z D×Fin k=>(pair t).val)
local notation "rt" => CoreRoute.stages banks p (CoreRoute.source s.sampler z W k attempts depth g.oldGroups dir.groups g.height R) s.sampler z W k attempts
variable (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank) (joint : JointHeader.Board)
  (scores : ℕ) (phase : Fin phases→PhasePrice) (v : Fin jobs→Market z (2^W) k) (raw : Boot.Tape z (2^W))
local notation "words" => chargedMasterWords E P empty order M groups dir joint scores depth phase π a idSrc amtSrc p o ci cj owners cat.rows raw
local notation "mid" => Boot.booted v size words
local notation "prior" => (fun t=>entryMemory C mid t)
local notation "endCore" => CoreRoute.stop s.sampler z W k attempts depth g.oldGroups dir.groups g.height R

include socket in
omit [Nonempty (Fin k)] in
theorem boot_settlement_local (headerOrder : E.Ordered) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (zeroBase : empty.base=P.stop)
    (bootLayout : Boot.Layout v size) (static : StaticSpace a p owners (rowOnlyCount c decl) r cat.rows w)
    (nphase : 0<phases) (tail : empty.base+empty.size≤a.kind.base) (wordEnd : owners.base+owners.size<2^w)
    (tape : owners.base+owners.size≤ size) (markets : ∀j,owners.base+owners.size≤Boot.low (v j))
    (first : 2^z≤joint.initial) (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (heap : Native.heapEnd z D Native.copies≤joint.initial) (coreEnd : endCore≤joint.initial)
    {J : Type*} [Fintype J] (other : PacketWidths J)
    (column : g.column=CoreCatalogue.top z W g.oldGroups dir.groups g.height R)
    (names : g.directory.remapBase=CoreCatalogue.groupStart z W)
    (sites : g.directory.sitesBase=CoreCatalogue.siteBase z W g.oldGroups)
    (supers : g.directory.superBase=CoreCatalogue.superStart z W) (bins : g.bins=dir.groups)
    (port : ∀a,E.ports.header 0=header F rows a)
    (outerLocal : ∀(i j : ℕ), Event.attempt (.outer i j)∈events c →
      PayloadLocal (K:=scale) (payload:=payload) F s c cat g i j (incoming (.outer i j)) C
        (prior (.outer i j)) (label (.outer i j)) finish fees other)
    (innerLocal : ∀(i : Fin (c.inject+c.cool)) (j : Fin c.outerFuel) (u : Fin c.reserveSteps) (t : Fin c.innerFuel),
      let e:=Attempt.inner i.val j.val u.val t.val
      PurchasedLocal F s c cat g i j u.val t.val (incoming e) C (prior e) (label e) π groups dir scale payload)
    (state : Word w) (pos : 0<num) (countFits : num<2^w) (reserveFits : fuel c*payload<2^w)
    (physical : ∀e,(B.row e).val=(order.symm e).val) (sinkRoom : SinkSpace sink w)
    (ar : Room c A L a banks num (rowOnlyCount c decl) w)
    (routeInput : (ReserveUse.word a banks).Fits w banks.kind.base) (coreFirst : endCore≤A.first)
    (flagEnd : A.endAddress c≤flag) (mounted : Calendar.mounted C (events c) mid)
    (floor : ∀t x,x<A.base c t→protected C x t) (span : ∀e∈events c,(L).rows e≤ownerArea.stride)
    (args : ∀t : Fin (events c).length,((L).term ((events c).get t)).Fits w (A.base c ((events c).get t)))
    (paidInputs : ∀e∈events c,((L).term e).Fits w banks.width.base)
    (amounts : ∀t : Fin (events c).length, pay ((events c).get t)+(L).rows ((events c).get t)≤A.base c ((events c).get t)+A.stride)
    (flagFit : (historyFlag C (events c)).Fits w flag) (flagWord : flag+1<2^w)
    (widthRoom : banks.width.base+cat.rows<2^w) (ownerEnd : ownerArea.endAddress c<2^w)
    (refOrder : A.first≤banks.kind.base) (bankWords : p.kind.Fits w banks.kind.base ∧ p.mode.Fits w banks.kind.base ∧ p.operand.Fits w banks.kind.base)
    (rc : 2*r≤2^w) (menu : Fintype.card (Actions N k)≤2^w)
    (kindCap : 2*r≤banks.kind.size) (idxCap : 2*r≤banks.index.size)
    (ki : banks.kind.base+2*r≤banks.index.base) (ix : banks.index.base+2*r<2^w)
    (recipesBelow : ∀«f»,(which p «f»).base+(which p «f»).size≤A.first)
    (ownerBelow : owners.base+owners.size≤A.first)
    (paidReady : PaidWidths.Mounted banks.width cat.rows paymentSource slices (checkedOut C flag mid)) :
    ∃ hw : ∀e,DatedBoard F s c cat g π groups dir e (prior e),
    let outer := fun i j active =>
      (⟨((outerLocal i j active).observe π groups dir bins (hw (.outer i j)).columns
        (hw (.outer i j)).input (hw (.outer i j)).port),rfl⟩ : {d : PayloadData (K:=scale) (payload:=payload) F s c cat g i j (incoming (.outer i j)) C (prior (.outer i j)) (label (.outer i j)) finish fees other // d.π=π})
    let inner := fun i j u t =>
      (⟨((innerLocal i j u t).observe (hw (.inner i.val j.val u.val t.val)).columns
        (hw (.inner i.val j.val u.val t.val)).port),rfl⟩ : {d : PurchasedData F s c cat g i j u.val t.val (incoming (.inner i.val j.val u.val t.val)) C (prior (.inner i.val j.val u.val t.val)) (label (.inner i.val j.val u.val t.val)) scale payload // d.permutation=π})
    let dates:=datesOfStrips (K:=scale) (payload:=payload) F s c cat g ownerArea C mid π incoming label finish fees other rfl outer inner
    let h:=issued dates
    let supply:=fuel c*payload
    let chk:=checkedOut C flag mid
    let use:=nativeSite L c h pos chk
    let bits:=debit c h
    let archive:=result rt (result ((L).scans c num) (PaidWidths.output banks.width cat.rows paymentSource slices chk))
    let closed:=ReserveUse.output a banks supply use bits archive
    let output:=(sink).output closed (enum B o) ci cj
    let cost:=terminalTime C L rt sink slices a num (rowOnlyCount c decl) supply
    let body:=(Native.subdivisionProgram z D).seq (terminal C L rt flag sink paymentSource slices a num (rowOnlyCount c decl) supply)
    let cpu:=machine body (flag:Word w)
    Whole.Reconciliation sink a supply use bits (enum B o) ci pair archive ∧
      body.Exec (Boot.initial v size words) output (Native.subdivisionConstant D*2^z+cost) ∧
      (∃ t≤Native.subdivisionConstant D*2^z+cost+2, ∃ done,
        advance cpu.program t (cpu.program.start state) (Boot.initial v size words)=some (done,output) ∧
        cpu.program.step done=.finish (some (output flag))) ∧
      ∀i : Fin num,RouteSettlement.actual banks.used closed i.val=(∑j,if site c h j=i then debit c h j else 0) ∧
        RouteSettlement.actual banks.reserved closed i.val=supply := by
  obtain ⟨_,_,seen,eco,_,_,_,_,_⟩ :=
    master_start_all E headerOrder P empty firstCharge secondCharge zeroBase order M groups dir joint scores depth phase π
      a idSrc amtSrc p o ci cj owners cat.rows raw v bootLayout socket static nphase tail wordEnd tape markets first scoreEnd heap coreEnd
  have h₁ : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have h₂ : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have h₃ : P.stop≤empty.base+empty.size:=zeroBase.ge.trans (Nat.le_add_right ..)
  have h₄:=static.reserveOrder
  have h₅:=static.routeStart
  have h₆:=static.kindEnd
  have h₇:=static.modeEnd
  have h₈:=static.operandEnd
  have headerLow : E.stop≤A.first:=by omega
  have word : A.first<2^w:=refOrder.trans_lt ((Nat.le_add_right ..).trans_lt
    (ki.trans_lt ((Nat.le_add_right ..).trans_lt ix)))
  let hw := fun e=>datedBoard F s c cat g π groups dir A C mid e order socket seen E headerOrder eco
    coreFirst headerLow word column names sites supers (port e) mounted floor
  refine ⟨hw,?_⟩
  dsimp only
  exact boot_settlement F s c cat g A ownerArea initialStock feedWidth cap finish fees banks src table dst owners
    flag paymentSource slices a p o order M groups dir socket π place B E P empty joint scores phase v raw headerOrder
    firstCharge secondCharge zeroBase bootLayout static nphase tail wordEnd tape markets first scoreEnd heap coreEnd other
    (fun i j active=>⟨(outerLocal i j active).observe π groups dir bins (hw _).columns (hw _).input (hw _).port,rfl⟩)
    (fun i j u t=>⟨(innerLocal i j u t).observe (hw _).columns (hw _).port,rfl⟩)
    state pos countFits reserveFits physical sinkRoom ar routeInput coreFirst flagEnd mounted floor span args paidInputs
    amounts flagFit flagWord widthRoom ownerEnd refOrder bankWords rc menu kindCap idxCap ki ix recipesBelow ownerBelow paidReady

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
