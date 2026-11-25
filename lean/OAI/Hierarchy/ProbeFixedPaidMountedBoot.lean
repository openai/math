import OAI.Hierarchy.ProbeFixedPaidMounted
import OAI.Hierarchy.ProtocolRAMCatalystPaidPairBoot
import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProbeFixedFailureWords

namespace OAI
/-! # Mount all original paid slices on the actual charged master tape and booted calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CatalystArchive StripChart CatalogueRows StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable {K G H R K₁ jobs size : ℕ} (z width : ℕ) (b : JointHeader.Board) (cat : CatalogueRows.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "N" => Stages z (2^v.W)
variable (order : Fin R≃Edges v.sampler z (2^v.W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^v.W))
  (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) H)
  (sockets : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) (π : Equiv.Perm (Fin (2^z))) (place : Site z (2^v.W) k→Fin K₁)
  (B : Mount (S:=v.sampler) π place cat.rows)
local notation "P" => v.catalystPlacement z K dir.groups H R b cat sockets
local notation "s" => v.nativeBoards P z width
local notation "E" => v.publicHeader P z width
local notation "A" => v.privateArena P z width
local notation "szBoard" => v.sized (v.seed P z width) width
local notation "prices" => v.basePhase width


open CoreRoute ColumnWires StockCommit StockBound
local notation "D" => 2^v.W
local notation "r" => Fintype.card (Slots z D k)
local notation "num" => Fintype.card (Columns z D)*k

/-- The fixed core and per-lane directories use two additional public pages in the same
master tape as the original paid economic header. This result can be applied at the
`paidReady` argument of `catalyst_run` with raw tape `PaidPairDirectory.mount ... raw`. -/
abbrev paid_booted_mount (stock : Bank) (maxBits : ℕ)
    (o : CoreRoute.Orders z D k) (markets : Fin jobs→Market z D k) (raw : Boot.Tape z D)
    (boot : Boot.Layout markets size) :=
  letI : Nonempty (Fin k) := ⟨⟨0,v.positive⟩⟩
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  let start:=v.catalystStaticStart P z width
  let declared:=declaredRows v.mesh (ownerLedger s v.mesh cat (P).routes F A)
  let count:=rowOnlyCount v.mesh declared
  let stride:=ownerRowFactor D k v.sampler.degree v.depth
    (max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k)))*2^z
  let page:=TerminalLayout.pageBits v.mesh A stock stride cat.rows r num count
  let banks:=TerminalLayout.settlement page stock
  let src:=TerminalLayout.source page
  let tab:=TerminalLayout.table page
  let dst:=TerminalLayout.destination page
  let owners:=sinkBank start count r cat.rows
  let ownArea:=TerminalLayout.ownerArea page stride
  let ledger:=ownerLedger s v.mesh cat (P).routes F ownArea
  let native:=v.nativeChart P z width r banks src tab dst owners
  let fmt:=v.nativeFormats P z width
  let g:=v.stamp P z width r banks src tab dst owners
  let charged:=StripChart.charges F szBoard v.cost (E).stop
  let empty:=v.emptyReserve P z width
  let freq:=DeadlineROM.prices v.mesh v.finish prices
  let ord : (E).Ordered:=economic_ordered F szBoard v.cost v.mesh b cat (P).routes v.finish prices
    v.digitRadix v.digitRadix v.precision v.precision
  let w:=Native.wordBits z D Native.copies
  let occ:=v.catalystPairOwners P z width
  let tag:=v.catalystPairParity P z width
  let paired:=PaidPairDirectory.mount occ tag r raw
  let a:=TerminalLayout.reserve start count page
  let recipe:=routeBanks start count r
  let ci:=(PurchaseInventory.slot : Commodity (Fin (2^z)) N k→ℕ)
  let cj:=fun t : Columns z D×Fin k=>(pairKeys (Columns z D) k t).val
  let incoming:=resolvedStock v.mesh A b.initial (build F (withPorts s v.mesh cat (P).routes))
  let pay:=cashWidthBase F s v.mesh cat (P).routes incoming
  let decl:=declaredRows v.mesh ledger
  let id:=rowOnly v.mesh decl (ownArea.base v.mesh)
  let amt:=rowOnly v.mesh decl pay
  let words:=chargedMasterWords E charged empty order M groups dir b N v.depth freq π a id amt recipe o ci cj owners cat.rows paired
  let mid:=Boot.booted markets size words
  let source:=CoreRoute.source v.sampler z v.W k n v.depth K dir.groups H R
  let tre:=v.nativeTrees P z width
  let fl:=FeedLayout.atEvent («N»:=N) v.mesh A fmt b.initial width v.keepLimit
  let fs:=feedColumns («N»:=N) v.mesh A fmt b.initial width v.keepLimit
  let corePath:=v.paidSpillPath P z width recipe source o
  let feedPath:=v.paidFeedPath P z width source fl
  let sink:=cat.sink r banks src tab dst owners
  let fields:=fun az=>(StripChart.header F s az).fieldTerm
  let ids:=StripChart.id F s cat
  let chk:=checkedOut native ((A).endAddress v.mesh) mid
  let top:=banks.width.base
  let staticLow:=v.catalyst_static_end P z width A
  fun (height : 28*2^page<2^w) (tape : owners.base+owners.size≤ size)
      (low : ∀j,owners.base+owners.size≤Boot.low (markets j))
      (first : 2^z≤b.initial) (heap : Native.heapEnd z D Native.copies≤b.initial)
      (core : CoreRoute.stop v.sampler z v.W k n v.depth K dir.groups H R≤b.initial)
      (mounted : Calendar.mounted native (events v.mesh) mid)
      (safe : Safe source v.sampler z v.W k n w top)
      (old : ∀az,Event.attempt az∈events v.mesh→(g az).edge.Fits w top ∧ (tre az).edge.Fits w top ∧
        (tre az).sourceRow.Fits w top ∧ ∀t∈(tre az).catalystMate,t.1.Fits w top ∧ t.2.Fits w top) =>
    show PaidWidths.Mounted banks.width cat.rows src (paidSlices v.mesh fmt fs sink cat.idBase fields ids tre corePath feedPath maxBits) chk from by
      have pageRoom : TerminalLayout.footprint v.mesh A stock stride cat.rows r num count<2^page:=Nat.lt_log2_self
      unfold TerminalLayout.footprint at pageRoom
      have arenaEnd : (A).first≤(A).endAddress v.mesh:=Nat.le_add_right ..
      have ownerEnd : owners.base+owners.size=(A).first:=staticLow
      have wide : owners.base+owners.size<2^w:=by omega
      have space:=allocated_space start count r cat.rows w a.history a.scratch wide
      have half:=v.reserve_before_catalystStaticStart P z width
      have init : empty.base+empty.size≤v.catalystPairStart P z width:=Nat.le_add_right ..
      have pairEnd : Slab.staticStart (v.catalystPairStart P z width) r≤a.kind.base:=le_rfl
      have data:=paid_pair_master E ord charged empty rfl rfl rfl order M groups dir b N v.depth freq π a id amt
        recipe o ci cj owners cat.rows raw markets boot sockets space
        (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) half wide tape low first le_rfl heap core
        (v.catalystPairStart P z width) init pairEnd
      have staticAt : start≤(A).first := v.catalyst_static_before P z width
      have before:=data.2.2 native A ((A).endAddress v.mesh) staticAt arenaEnd
        (fun e x hx=>(v.event_prefix P z width r banks src tab dst owners e x hx).1) mounted
      have financial : top=2^page:=by change 1*_= _; exact Nat.one_mul _
      have fits (c : Bank) (endAt : c.base+c.size≤owners.base) : c.Fits w top:=
        ⟨Nat.two_pow_pos _,by omega,by omega⟩
      have operandEnd : recipe.operand.base+recipe.operand.size≤owners.base := space.operandEnd
      have modeEnd : recipe.mode.base+recipe.mode.size≤owners.base :=
        space.modeEnd.trans ((Nat.le_add_right recipe.operand.base recipe.operand.size).trans operandEnd)
      have kindEnd : recipe.kind.base+recipe.kind.size≤owners.base :=
        space.kindEnd.trans ((Nat.le_add_right recipe.mode.base recipe.mode.size).trans modeEnd)
      have recipeFit : recipe.kind.Fits w top ∧ recipe.mode.Fits w top ∧ recipe.operand.Fits w top :=
        ⟨fits _ kindEnd,fits _ modeEnd,fits _ operandEnd⟩
      exact v.paid_mounted_at P z width stock stride num count maxBits source recipe o owners mid
        data.1 mounted before height staticAt safe recipeFit old


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
