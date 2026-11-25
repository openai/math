import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProtocolRAMCalendarDatedSeparation
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMachine
import OAI.Hierarchy.ProtocolRAMCatalystStripRunLocal
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMCatalystStripOwnerCost

namespace OAI
/-! # Actual strip settlement on the canonical terminal banks -/

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
  (cat : CatalogueRows.Board) (g : PortBanks ((c.inject+c.cool)*c.outerFuel)) (A : Arena) (stock : Bank) (terminalStart : ℕ)
  (initialStock feedWidth cap : ℕ) (finish : ℝ) (fees : PhasePrice) (slices : List PaidWidths.Slice)
  (o : Orders z (2^W) k)
  (order : Fin R≃Edges s.sampler z (2^W) k) (M : ℕ) (groups : Fin g.oldGroups≃AllGroups z (2^W))
local notation "attempts" => (c.inject+c.cool)*c.outerFuel
variable (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))) g.height)
  (socket : BoughtSockets.Directory ((c.inject+c.cool)*c.outerFuel)) (π : Equiv.Perm (Fin (2^z))) (place : Site z (2^W) k→Fin K₁)
  (B : Mount (S:=s.sampler) π place cat.rows)
local notation "publicCount" => rowOnlyCount c (declaredRows c (ownerLedger s c cat g F A))
local notation "ownerStride" => ownerRowFactor D k s.sampler.degree depth
  (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k)))*2^z
local notation "pageWidth" => TerminalLayout.pageBits c A stock ownerStride cat.rows r num publicCount
local notation "ownerArea" => TerminalLayout.ownerArea pageWidth ownerStride
local notation "nativeBanks" => TerminalLayout.settlement pageWidth stock
local notation "src" => TerminalLayout.source pageWidth
local notation "table" => TerminalLayout.table pageWidth
local notation "dst" => TerminalLayout.destination pageWidth
local notation "owners" => sinkBank terminalStart publicCount r cat.rows
local notation "flag" => A.endAddress c
local notation "archiveBank" => TerminalLayout.reserve terminalStart publicCount pageWidth
local notation "recipes" => routeBanks terminalStart publicCount r
local notation "rows" => withPorts s c cat g
local notation "sink" => cat.sink r nativeBanks src table dst owners
local notation "C" => chart F c A initialStock feedWidth cap rows finish fees cat r nativeBanks src table dst owners
local notation "L" => ownerLedger s c cat g F ownerArea
local notation "incoming" => resolvedStock c A initialStock (build F rows)
local notation "pay" => cashWidthBase F s c cat g incoming
local notation "decl" => declaredRows c L
local notation "idSrc" => rowOnly c decl ((ownerArea).base c)
local notation "amtSrc" => rowOnly c decl pay
local notation "f" => formats F c A initialStock rows
local notation "label" => (fun t=> (f t).labelSource sink cat.idBase (header F rows t).fieldTerm (id F rows cat t))
local notation "pair" => pairKeys (CoreBoard.Columns z D) k
local notation "ci" => (PurchaseInventory.slot : Commodity (Fin (2^z)) N k→ℕ)
local notation "cj" => (fun t : CoreBoard.Columns z D×Fin k=>(pair t).val)
local notation "rt" => CoreRoute.stages nativeBanks recipes (CoreRoute.source s.sampler z W k attempts depth g.oldGroups dir.groups g.height R) s.sampler z W k attempts
variable (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank) (joint : JointHeader.Board)
  (scores : ℕ) (phase : Fin phases→PhasePrice) (v : Fin jobs→Market z (2^W) k) (raw : Boot.Tape z (2^W))
local notation "words" => chargedMasterWords E P empty order M groups dir joint scores depth phase π archiveBank idSrc amtSrc recipes o ci cj owners cat.rows raw
local notation "mid" => Boot.booted v size words
local notation "prior" => (fun t=>entryMemory C mid t)
local notation "endCore" => CoreRoute.stop s.sampler z W k attempts depth g.oldGroups dir.groups g.height R

include socket in
omit [Nonempty (Fin k)] in
theorem boot_allocated_boards (headerOrder : E.Ordered) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (zeroBase : empty.base=P.stop)
    (bootLayout : Boot.Layout v size) (nphase : 0<phases) (tail : empty.base+empty.size≤terminalStart)
    (staticLow : (owners).base+(owners).size≤A.first)
    (geometry : ∀i,(cat.geometry i).Fits w (A.endAddress c)) (height : 28*2^pageWidth<2^w)
    (tape : (owners).base+(owners).size≤ size) (markets : ∀j,(owners).base+(owners).size≤Boot.low (v j))
    (first : 2^z≤joint.initial) (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (heap : Native.heapEnd z D Native.copies≤joint.initial) (coreEnd : endCore≤joint.initial)
    (column : g.column=CoreCatalogue.top z W g.oldGroups dir.groups g.height R)
    (names : g.directory.remapBase=CoreCatalogue.groupStart z W)
    (sites : g.directory.sitesBase=CoreCatalogue.siteBase z W g.oldGroups)
    (supers : g.directory.superBase=CoreCatalogue.superStart z W)
    (port : ∀a,E.ports.header 0=header F rows a)
    (mounted : Calendar.mounted C (events c) mid) (floor : ∀t x,x<A.base c t→protected C x t) :
    ∀e,DatedBoard F s c cat g π groups dir e (prior e) := by
  have geom:=TerminalLayout.allocated c A L cat z W k num publicCount terminalStart ownerStride w stock rfl staticLow geometry height
  have cashEnd : A.first≤A.endAddress c:=Nat.le_add_right ..
  have firstRoom : A.first<2^w:=(cashEnd.trans (Nat.le_succ _)).trans_lt geom.flagWord
  have wordEnd : (owners).base+(owners).size<2^w:=staticLow.trans_lt firstRoom
  have static := allocated_space terminalStart publicCount r cat.rows w (⟨0,pageWidth+2⟩ : Bank) (8*2^pageWidth) wordEnd
  have rootStart : terminalStart≤A.first:=(Nat.le_add_right terminalStart _).trans
    (TerminalLayout.static_below terminalStart publicCount r cat.rows A staticLow).2
  have p₀ : E.ports.base≤E.stop:=(Nat.le_add_right ..).trans (economic_ports_end E headerOrder)
  have p₁ : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have p₂ : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have p₃ : P.stop≤empty.base+empty.size:=zeroBase.ge.trans (Nat.le_add_right ..)
  have headerLow := p₁.trans (p₂.trans (p₃.trans (tail.trans rootStart)))
  have scoreStarts : joint.initial≤JointHeader.stop joint z scores k phases :=
    (Nat.le_add_right ..).trans ((JointHeader.order joint z scores k).trans (Nat.le_add_right ..))
  have coreFirst : endCore≤A.first:=coreEnd.trans (scoreStarts.trans (scoreEnd.trans (p₀.trans headerLow)))
  obtain ⟨_,_,seen,eco,_,_,_,_,_⟩:=master_start_all E headerOrder P empty firstCharge secondCharge zeroBase
    order M groups dir joint scores depth phase π archiveBank idSrc amtSrc recipes o ci cj owners cat.rows raw v
    bootLayout socket static nphase tail wordEnd tape markets first scoreEnd heap coreEnd
  intro e
  exact datedBoard F s c cat g π groups dir A C mid e order socket seen E headerOrder eco coreFirst headerLow
    firstRoom column names sites supers (port e) mounted floor

set_option maxHeartbeats 800000 in
include socket in
omit [Nonempty (Fin k)] in
theorem boot_settlement_allocated (headerOrder : E.Ordered) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (zeroBase : empty.base=P.stop)
    (bootLayout : Boot.Layout v size) (nphase : 0<phases) (tail : empty.base+empty.size≤terminalStart)
    (staticLow : (owners).base+(owners).size≤A.first)
    (geometry : ∀i,(cat.geometry i).Fits w (A.endAddress c)) (height : 28*2^pageWidth<2^w)
    (tape : (owners).base+(owners).size≤ size) (markets : ∀j,(owners).base+(owners).size≤Boot.low (v j))
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
    (state : Word w) (pos : 0<num) (reserveFits : fuel c*payload<2^w)
    (physical : ∀e,(B.row e).val=(order.symm e).val) (mounted : Calendar.mounted C (events c) mid)
    (floor : ∀t x,x<A.base c t→protected C x t)
    (args : ∀t : Fin (events c).length,((L).term ((events c).get t)).Fits w (A.base c ((events c).get t)))
    (amounts : ∀t : Fin (events c).length, pay ((events c).get t)+(L).rows ((events c).get t)≤A.base c ((events c).get t)+A.stride)
    (dated : ∀t,Event.attempt t∈events c→(repair C t).verdict<A.base c (.attempt t)+A.stride)
    (menu : Fintype.card (Actions N k)≤2^w)
    (paidReady : PaidWidths.Mounted (nativeBanks).width cat.rows src slices (checkedOut C flag mid)) :
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
    let archive:=result rt (result ((L).scans c num) (PaidWidths.output (nativeBanks).width cat.rows src slices chk))
    let closed:=ReserveUse.output archiveBank nativeBanks supply use bits archive
    let output:=(sink).output closed (enum B o) ci cj
    let cost:=terminalTime C L rt sink slices archiveBank num (rowOnlyCount c decl) supply
    let body:=(Native.subdivisionProgram z D).seq (terminal C L rt flag sink src slices archiveBank num (rowOnlyCount c decl) supply)
    let cpu:=machine body (flag:Word w)
    Whole.Reconciliation sink archiveBank supply use bits (enum B o) ci pair archive ∧
      body.Exec (Boot.initial v size words) output (Native.subdivisionConstant D*2^z+cost) ∧
      (∃ t≤Native.subdivisionConstant D*2^z+cost+2, ∃ done,
        advance cpu.program t (cpu.program.start state) (Boot.initial v size words)=some (done,output) ∧
        cpu.program.step done=.finish (some (output flag))) ∧
      (∀i : Fin num,RouteSettlement.actual (nativeBanks).used closed i.val=(∑j,if site c h j=i then debit c h j else 0) ∧
        RouteSettlement.actual (nativeBanks).reserved closed i.val=supply) ∧
      (output flag=0 ↔ Calendar.admissible C (events c) mid) := by
  have geom:=TerminalLayout.allocated c A L cat z W k num publicCount terminalStart ownerStride w stock rfl staticLow geometry height
  have cashEnd : A.first≤A.endAddress c:=Nat.le_add_right ..
  have firstRoom : A.first<2^w:=cashEnd.trans_lt (by have :=geom.flagWord;omega)
  have wordEnd : (owners).base+(owners).size<2^w:=staticLow.trans_lt firstRoom
  have static := allocated_space terminalStart publicCount r cat.rows w (⟨0,pageWidth+2⟩ : Bank) (8*2^pageWidth) wordEnd
  have rootStart : terminalStart≤A.first := by
    have endAt:=(TerminalLayout.static_below terminalStart publicCount r cat.rows A staticLow).2
    omega
  have scoreStarts : joint.initial≤JointHeader.stop joint z scores k phases :=
    (Nat.le_add_right ..).trans ((JointHeader.order joint z scores k).trans (Nat.le_add_right ..))
  have p₀ : E.ports.base≤E.stop:=(Nat.le_add_right ..).trans (economic_ports_end E headerOrder)
  have p₁ : E.stop≤P.payload.stop:=firstCharge.ge.trans (Nat.le_add_right ..)
  have p₂ : P.payload.stop≤P.stop:=secondCharge.ge.trans (Nat.le_add_right ..)
  have p₃ : P.stop≤empty.base+empty.size:=zeroBase.ge.trans (Nat.le_add_right ..)
  have coreFirst : endCore≤A.first:=coreEnd.trans (scoreStarts.trans (scoreEnd.trans
    (p₀.trans (p₁.trans (p₂.trans (p₃.trans (tail.trans rootStart)))))))
  have span (e : Event) (_ : e∈events c) : (L).rows e≤(ownerArea).stride :=
    ledger_owner_rows s c cat g F ownerArea e
  have paidInputs (e : Event) (found : e∈events c) : ((L).term e).Fits w (nativeBanks).width.base := by
    obtain ⟨t,eq⟩ := List.mem_iff_get.mp found
    have sourceFit := args t
    rw [eq] at sourceFit
    have last := A.within c e found
    exact ProtocolRAMGeneratedWrite.fits_mono _ ((Nat.le_add_right ..).trans (last.trans geom.archive.cash)) sourceFit
  have wide : 0<w := by have :=geom.sink.wide;omega
  have flagFit := historyFlag_fits_of_dated C A wide dated
  have separate := separated_of_dated C A floor dated
  have belowRoute (pass : Pass) (hp : pass∈rt) : flag<pass.out := by
    have early : flag<1*2^pageWidth:=geom.flagLow.2.2.2.2.1
    simp only [CoreRoute.stages,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl
    · change flag<4*2^pageWidth
      omega
    · change flag<5*2^pageWidth
      omega
  obtain ⟨hw,result⟩:=boot_settlement_local F s c cat g A ownerArea initialStock feedWidth cap finish fees nativeBanks
    src table dst owners flag src slices archiveBank recipes o order M groups dir socket π place B
    E P empty joint scores phase v raw headerOrder firstCharge secondCharge zeroBase bootLayout static
    nphase tail wordEnd tape markets first scoreEnd heap coreEnd other column names sites supers bins port
    outerLocal innerLocal state pos geom.countWord reserveFits physical geom.sink geom.archive geom.readers
    coreFirst le_rfl mounted floor span args paidInputs amounts flagFit geom.flagWord geom.widthRoom geom.ownerEnd
    geom.refOrder ⟨geom.recipes .kind,geom.recipes .mode,geom.recipes .operand⟩ geom.rows menu
    geom.kindSize geom.indexSize geom.order geom.indexWord geom.recipeLow geom.ownerLow paidReady
  refine ⟨hw,?_⟩
  dsimp only at result ⊢
  refine ⟨result.1,result.2.1,result.2.2.1,result.2.2.2,?_⟩
  exact terminal_verdict C L rt flag sink src slices archiveBank _ pos (enum B o) ci pair mid mounted
    separate wide paidReady geom.sink.width belowRoute geom.flagLow

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
