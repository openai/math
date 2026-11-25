import OAI.Hierarchy.ProbeFixedUniformCalendar
import OAI.Hierarchy.ProbeFixedBroadcastCap
import OAI.Hierarchy.ProbeFixedUniformSink
import OAI.Hierarchy.ProbeFixedWideOwnerRoutes
import OAI.Hierarchy.ProbeFixedWidePaidClock
import OAI.Hierarchy.ProbeFixedWideFromCT
import OAI.Hierarchy.ProbeStageCompactProgram

namespace OAI
/-! # Fixed program size and linear instruction time of the complete paid controller -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "last" => (events v.mesh).length
open ProbeStage.Native

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
/-- Price every terminal stage from its actual chronological program. The cap
on funded bits is the word-room condition used by the actual paid-width scan. -/
theorem wide_after_ct_resources (bits : ℕ) :
    ∃K : ℕ,∀h width,v.keepLimit*width+1≤2^h →
      v.wideAfterCTTime h width bits≤K*2^h ∧ text (v.wideAfterCT h width bits)≤K := by
  obtain ⟨calendar,checked⟩:=v.wide_checked_resources
  obtain ⟨sinkBound,sinkCharge⟩:=v.wideSinkBill
  let rr:=resourceFactor D k
  let ar:=stripRecordFactor v.mesh D k v.sampler.degree v.depth
  let K:=calendar+v.widePaidClockFactor bits+v.wideOwnerRouteBill+19+12*rr+160*ar+
    sinkBound+30+v.wideSliceLength*(33+4*v.wideIssueCost bits)+218
  refine ⟨K,?_⟩
  intro h width budget
  let placement := v.widePlacement h width
  let boards := v.nativeBoards placement h width
  let arena := v.privateArena placement h width
  let start := v.catalystStaticStart placement h width
  let count := Fintype.card (Columns h D)*k
  let slots := Fintype.card (Slots h D k)
  let records := rowOnlyCount v.mesh
    (declaredRows v.mesh (ownerLedger boards v.mesh placement.catalogue placement.routes F arena))
  let stride := ownerRowFactor D k v.sampler.degree v.depth
    (max (Fintype.card (StripDirectory.PayloadRole (Stages h D) k))
      (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h
  let stock := v.fixedTerminalStock placement h width
  let page := v.wideSignedPage h width stock
  let banks := TerminalLayout.settlement page stock
  let ledger := ownerLedger boards v.mesh placement.catalogue placement.routes F (TerminalLayout.ownerArea page stride)
  let geometry := CoreRoute.source v.sampler h v.W k v.wideJobs v.depth (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs) (WideMemory.R v.sampler h v.W k)
  let routes := CoreRoute.stages banks (routeBanks start records slots) geometry v.sampler h v.W k v.wideJobs
  let original := TerminalLayout.reserve start records page
  let supply := fuel v.mesh*width
  let ctl := v.wideSignedChart h width stock
  let sink := v.wideSink h width
  let ss := v.widePaidSlices h width bits
  have pos : 1≤2^h := Nat.one_le_two_pow
  have ca := checked h width (arena.endAddress v.mesh)
  have paid := v.wide_paid_clock h width bits budget
  have tour := v.wide_owner_route_resources h width (count:=count)
  have sk := sinkCharge h width
  have coord : count≤rr*2^h := physical_resources h D k Nat.one_le_two_pow
  have hist : records≤ar*2^h := declared_records boards v.mesh placement.catalogue placement.routes F arena
  have res : ReserveUse.clock original banks count records supply≤(19+12*rr+160*ar)*2^h := by
    rw [ReserveUse.clock_eq]
    simpa only [Nat.add_mul,Nat.mul_assoc,Nat.mul_one] using
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 19 pos) (Nat.mul_le_mul_left 12 coord))
        (Nat.mul_le_mul_left 160 hist)
  constructor
  · change checkedCost ctl+PaidWidths.clock banks.width placement.catalogue.rows ss+
      ProtocolRAM.clock (ledger.scans v.mesh count)+ProtocolRAM.clock routes+
      ReserveUse.clock original banks count records supply+sink.clock≤K*2^h
    have total := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ca.1 paid.1) tour.1) res) sk.1
    have tariff : calendar+v.widePaidClockFactor bits+v.wideOwnerRouteBill+(19+12*rr+160*ar)+sinkBound≤K := by
      dsimp only [K]
      omega
    apply le_trans _ (Nat.mul_le_mul_right (2^h) tariff)
    simpa only [Nat.add_mul,Nat.add_assoc] using total
  · change text (CatalystArchive.terminal ctl ledger routes (arena.endAddress v.mesh) sink (TerminalLayout.source page)
      ss original count records supply)≤K
    simp only [CatalystArchive.terminal,text_seq,text_passes,paid_text,PrefixReserve.native_text]
    change text (Calendar.checked ctl (arena.endAddress v.mesh))+
      (30+(ss.map (fun t=>rowText (RepairHistogram.pair (t.columns banks.width placement.catalogue.rows))+22)).sum)+
      listText (ledger.scans v.mesh count)+listText routes+218+
      text (sink.native (Native.wordBits h D Native.copies))≤K
    have total := Nat.add_le_add (Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add ca.2 (Nat.add_le_add_left paid.2 30)) tour.2) 218)
      (sk.2 (Native.wordBits h D Native.copies))
    have tariff : calendar+(30+v.wideSliceLength*(33+4*v.wideIssueCost bits))+v.wideOwnerRouteBill+218+sinkBound≤K := by
      dsimp only [K]
      omega
    apply le_trans _ tariff
    simpa only [Nat.add_assoc] using total

/-- The uniform tariff uses the maximum selector-charge code from the two
original finite packet menus. The CPU word size and the ballast width may grow. -/
theorem wide_compact_resources :
    ∃K : ℕ,∀h width,v.keepLimit*width+1≤2^h →
       v.wideFromCTTime h width v.maxBits (Compact.constant D*2^h)≤K*2^h ∧
       text (v.wideFromCT h width v.maxBits (Compact.subdivision h D))≤K := by
  obtain ⟨C,bill⟩:=v.wide_after_ct_resources v.maxBits
  let K:=Compact.constant D+Compact.codeBound D+((events v.mesh).length+2)*C
  refine ⟨K,?_⟩
  intro h width budget
  obtain ⟨time,code⟩:=bill h width budget
  have head:=Compact.subdivision_text h D
  have whole:=v.wide_from_ct_price h width v.maxBits (Compact.subdivision h D) (Compact.constant D*2^h)
  have step:=Nat.mul_le_mul_left (last+2) time
  have size:=Nat.mul_le_mul_left (last+2) code
  constructor
  · refine whole.1.trans ?_
    calc
      _ ≤ Compact.constant D*2^h+(last+2)*(C*2^h) := Nat.add_le_add_left step _
      _ = (Compact.constant D+(last+2)*C)*2^h := by ring
      _ ≤ K*2^h := Nat.mul_le_mul_right _ (by dsimp only [K]; omega)
  · apply whole.2.trans
    dsimp only [K]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
