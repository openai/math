import OAI.Hierarchy.ProtocolRAMCatalystMasterSettle
import OAI.Hierarchy.ProtocolRAMCatalystStripDates
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe
import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Execution from the common economic header through both dated strips and settlement -/

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
  (order : Fin R≃Edges s.sampler z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
local notation "attempts" => (c.inject+c.cool)*c.outerFuel
variable (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) H)
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
local notation "rt" => CoreRoute.stages banks p (CoreRoute.source s.sampler z W k attempts depth K dir.groups H R) s.sampler z W k attempts
variable (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank) (joint : JointHeader.Board)
  (scores : ℕ) (phase : Fin phases→PhasePrice) (v : Fin jobs→Market z (2^W) k) (raw : Boot.Tape z (2^W))
local notation "words" => chargedMasterWords E P empty order M groups dir joint scores depth phase π a idSrc amtSrc p o ci cj owners cat.rows raw
local notation "mid" => Boot.booted v size words
local notation "prior" => (fun t=>entryMemory C mid t)
local notation "endCore" => CoreRoute.stop s.sampler z W k attempts depth K dir.groups H R

include socket in
omit [Nonempty (Fin k)] in
/-- The source is the literal subdivision boot with the authentic permutation, native menus,
zero account, priced cash arrays and public route operands. The output includes the true
processor run and all signed reserve counters, also for rejected calendar histories. -/
theorem boot_settlement (headerOrder : E.Ordered) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (zeroBase : empty.base=P.stop)
    (bootLayout : Boot.Layout v size) (static : StaticSpace a p owners (rowOnlyCount c decl) r cat.rows w)
    (nphase : 0<phases) (tail : empty.base+empty.size≤a.kind.base) (wordEnd : owners.base+owners.size<2^w)
    (tape : owners.base+owners.size≤ size) (markets : ∀j,owners.base+owners.size≤Boot.low (v j))
    (first : 2^z≤joint.initial) (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (heap : Native.heapEnd z D Native.copies≤joint.initial) (coreEnd : endCore≤joint.initial)
    {J : Type*} [Fintype J] (other : PacketWidths J)
    (outer : ∀(i j : ℕ), Event.attempt (.outer i j)∈events c →
      {d : PayloadData (K:=scale) (payload:=payload) F s c cat g i j (incoming (.outer i j)) C
        (prior (.outer i j)) (label (.outer i j)) finish fees other // d.π=π})
    (inner : ∀(i : Fin (c.inject+c.cool)) (j : Fin c.outerFuel) (u : Fin c.reserveSteps) (t : Fin c.innerFuel),
      let e:=Attempt.inner i.val j.val u.val t.val
      {d : PurchasedData F s c cat g i j u.val t.val (incoming e) C (prior e) (label e) scale payload // d.permutation=π})
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
  dsimp only
  let dates := datesOfStrips (K:=scale) (payload:=payload) F s c cat g ownerArea C mid π incoming label finish fees other rfl outer inner
  obtain ⟨started,boot,seen,eco,charges,prices,free,installed,_⟩ :=
    master_start_all E headerOrder P empty firstCharge secondCharge zeroBase order M groups dir joint scores depth phase π
      a idSrc amtSrc p o ci cj owners cat.rows raw v bootLayout socket static nphase tail wordEnd tape markets first scoreEnd heap coreEnd
  have actualN := recordCount_rowOnly c (issued dates) decl (issued_rows dates)
  have scalar : Room (C).mesh A L a banks num (recordCount (C).mesh (issued dates)) w := by
    change Room c A L a banks num (recordCount c (issued dates)) w
    rw [actualN]
    exact ar
  have amountBound (t : Fin (events c).length) (j : Fin (atTime c (issued dates) t).rows) :
      a.history.base+pay ((events c).get t)+j.val<A.base c ((events c).get t)+A.stride := by
    rw [ar.zero,Nat.zero_add]
    exact (Nat.add_lt_add_left (j.isLt.trans_eq (issued_shape dates t (fun _=>rfl))) _).trans_le (amounts t)
  have safe := source_safe s.sampler z W k attempts depth K dir.groups H R w banks.kind.base
    (coreFirst.trans refOrder) (by omega)
  have settled := master_settle C A L pay flag raw mid dates (fun _=>rfl) sink paymentSource slices a pos
    countFits reserveFits p π place B order o seen coreFirst physical ci pair sinkRoom scalar routeInput flagEnd
    mounted floor span args paidInputs amountBound flagFit flagWord widthRoom ownerEnd safe bankWords rc menu
    kindCap idxCap ki ix installed recipesBelow ownerBelow (ownerBelow.trans refOrder) paidReady
  let cost:=terminalTime C L rt sink slices a num (rowOnlyCount c decl) (fuel c*payload)
  let body:=terminal C L rt flag sink paymentSource slices a num (rowOnlyCount c decl) (fuel c*payload)
  obtain ⟨reconciled, ran, counters⟩ := settled
  let execution (n : ℕ) (out : Memory w) : Prop :=
    (terminal C L rt flag sink paymentSource slices a num n (fuel c*payload)).Exec mid out
      (terminalTime C L rt sink slices a num n (fuel c*payload))
  have declared {out : Memory w} (actual : execution (recordCount c (issued dates)) out) :
      execution (rowOnlyCount c decl) out :=
    (congrArg (fun n => execution n out) actualN).mp actual
  have both : ((Native.subdivisionProgram z D).seq body).Exec (Boot.initial v size words) _
      (Native.subdivisionConstant D*2^z+cost) :=
    Procedure.Exec.then (b:=mid) started (declared ran)
  obtain ⟨t, bound, done, stopped, readFlag⟩ :=
    machine_run ((Native.subdivisionProgram z D).seq body) (flag:Word w) state _ _ _ both
  rw [Fin.val_cast_of_lt ((Nat.lt_succ_self flag).trans flagWord)] at readFlag
  exact ⟨reconciled,both,⟨t,bound,done,stopped,readFlag⟩,counters⟩

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
