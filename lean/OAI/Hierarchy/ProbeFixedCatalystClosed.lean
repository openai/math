import OAI.Hierarchy.ProbeFixedCatalystSettlement
import OAI.Hierarchy.ProbeFixedCatalystPayloadLocal
import OAI.Hierarchy.ProbeFixedCatalystPurchasedLocal
import OAI.Hierarchy.ProbeFixedStockWindow
import OAI.Hierarchy.ProbeFixedStockPrefixFits
import OAI.Hierarchy.ProbeFixedCatalystStaticEnd
import OAI.Hierarchy.ProbeFixedCatalystOwnerFits
import OAI.Hierarchy.ProbeFixedCatalystEventRoom

namespace OAI
/-! # Reconciliation of the signed rows selected by the fixed native execution -/

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

private theorem inside (c : Mesh) (p : Fin (c.inject+c.cool)) (a : Fin c.outerFuel)
    (j : Fin c.reserveSteps) (t : Fin c.innerFuel) :
    Event.attempt (.inner p.val a.val j.val t.val)∈events c := by
  apply List.mem_flatMap.mpr
  refine ⟨p.val,List.mem_range.mpr p.isLt,List.mem_append_left _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨a.val,List.mem_range.mpr a.isLt,List.mem_cons_of_mem _ ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨j.val,List.mem_range.mpr j.isLt,List.mem_append_left _ ?_⟩
  exact List.mem_map.mpr ⟨t.val,List.mem_range.mpr t.isLt,rfl⟩

/-- The two local debit entries are built from the original outer and inner times, the
literal stored ballot, and the one common boot. A purchase uses its actual earlier
outer birth board, even when intervening attempts overwrite the active repair bank. -/
abbrev catalyst_run (stock : Bank) (slices : List PaidWidths.Slice)
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
  let addr:=v.catalystPlacement_addresses z K dir.groups H R b cat sockets
  let run:=v.catalyst_settlement z width b cat order M groups dir sockets π place B stock start slices o markets raw boot
  let tail:=v.reserve_before_catalystStaticStart P z width
  let staticLow : owners.base+owners.size≤(A).first:=(v.catalyst_static_end P z width A).le
  fun geometry height tape low first heap core state physical mounted
      (late : v.stripHeight≤z) (small : width≤2^z) (calibrated : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z)
      (clockRoom : max (max (fuel v.mesh) v.keepLimit) (Fintype.card (Actions (publicStages v.W) k))≤z)
      (jointBudget : v.keepLimit*width≤b.cap*b.width)
      (board : ∀a,Event.attempt a∈events v.mesh→PurchaseStage.Board (native.layout a) (repair native a)
        (Native.wordBits z D Native.copies)) paidReady =>
    letI : Nonempty (Columns z D):=⟨.inl ⟨0,Nat.two_pow_pos _⟩⟩
    let pos : 0<num:=Nat.mul_pos Fintype.card_pos v.positive
    let w:=Native.wordBits z D Native.copies
    have formatRoom:=TerminalLayout.allocated v.mesh A ledger cat z v.W k num count start stride w stock rfl staticLow geometry height
    have arenaRoom : (A).endAddress v.mesh<2^w:=by have :=formatRoom.flagWord;omega
    have wide : z<2^z:=Nat.lt_two_pow_self
    have multiplied (factor : ℕ) (bound : factor≤z) : factor*width<2^w:=by
      calc
        _≤2^z*2^z:=Nat.mul_le_mul (bound.trans wide.le) small
        _=2^(z+z):=(pow_add ..).symm
        _<2^w:=Nat.pow_lt_pow_right (by decide) (by dsimp only [w];rw [Native.wordBits_linear];omega)
    have limit : max (fuel v.mesh) v.keepLimit≤z:=(le_max_left ..).trans clockRoom
    have reserved:=multiplied (fuel v.mesh) ((le_max_left ..).trans limit)
    have keys:=v.election_key_room z K dir.groups H R b cat sockets core
    let window:=fun a active=>v.stock_trial_layout P z width r banks src tab dst owners a active arenaRoom
      (multiplied v.keepLimit ((le_max_right ..).trans limit)) jointBudget
      (v.stock_prefix_native P z width a keys) (board a active)
    have menu : Fintype.card (Actions N k)≤2^w:=by
      rw [show N=publicStages v.W from fixed_stage_count z v.W]
      exact (le_max_right ..).trans (clockRoom.trans (wide.le.trans (v.date_prefix_fit z).le))
    let floor:=fun e x hx=>(v.event_prefix P z width r banks src tab dst owners e x hx).1
    let hw:=boot_allocated_boards F s v.mesh cat (P).routes A stock start b.initial width v.keepLimit v.finish prices
      o order M groups dir sockets π E charged empty b N freq markets raw ord rfl rfl rfl boot
      (by exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) tail staticLow geometry height tape low first le_rfl heap core
      addr.1 addr.2.1 addr.2.2.1 addr.2.2.2.1 (v.catalyst_header P z width) mounted floor
    let outer:=fun phase trial active=>v.payloadLocal P z width r banks src tab dst owners _ phase trial late small
      mounted active pos (window (.outer phase trial) active) calibrated
    let inner:=fun i j u t=>(v.purchasedLocalAtBirth (R:=R) z width b cat groups dir sockets r banks src tab dst owners
      _ π i j u t mounted late small heap core (hw (.outer i j)) calibrated
      (window (.inner i j u t) (inside v.mesh i j u t))).val
    run tail staticLow geometry height tape low first heap core outer inner state pos reserved physical mounted
      floor (v.catalyst_owner_args z width K dir.groups H R b cat sockets ownArea core arenaRoom)
      (fun i=>v.catalyst_amount_room P z width ownArea ((events v.mesh).get i))
      (fun a _=>v.catalyst_dated_verdict P z width r banks src tab dst owners a) menu paidReady

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
