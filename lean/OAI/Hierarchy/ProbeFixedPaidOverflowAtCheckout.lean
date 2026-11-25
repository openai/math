import OAI.Hierarchy.ProbeFixedPaidOverflowCells
import OAI.Hierarchy.ProbeFixedAttemptSpill
import OAI.Hierarchy.ProbeFixedReadbackProducer

namespace OAI
/-! # Both paid overflow classes at the original live signed checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute
open CatalystArchive StripChart CatalogueRows ColumnWires PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W

/-- Every native attempted repair reads its paid overflow from its own
original slab. All later trials, feeds, and the final guard preserve that value. -/
theorem paid_attempt_cells :
    ∀ᶠ z : ℕ in Filter.atTop,∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (π : Equiv.Perm (Fin (2^z)))
      (mem fixture : Memory (Native.wordBits z (2^v.W) Native.copies)),
      v.ReadbackRun P z width r banks src tab dst owners π mem fixture →
      let C:=v.nativeChart P z width r banks src tab dst owners
      let A:=v.privateArena P z width
      ∀a,Event.attempt a∈events v.mesh→let ar:=(v.nativeFormats P z width a).pricedArea
        ∀i : Fin ar.goods,((checkedOut C (A.endAddress v.mesh) mem)
          (ar.output+ar.goods+ar.goods+i.val)).val≤v.menu.maximum*width := by
  filter_upwards [v.attempt_spill_bound] with z number
  intro P width r banks src tab dst owners π mem fixture receipt C A a live ar i
  obtain ⟨prior,tail,h⟩:=List.append_of_mem live
  let entry:=Calendar.run C prior mem
  have cut:=slot_of_split C mem (.attempt a) prior tail entry h rfl receipt.nativeStock.mounted_all
  rw [v.paid_attempt_cell_at P z width r banks src tab dst owners a mem entry prior tail cut i]
  exact number P width r banks src tab dst owners π mem fixture receipt a prior tail entry cut i

theorem wide_paid_overflow_cells :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ width, width ≤ 2^h → v.widthFloor ≤ width → v.keepLimit*width+1 ≤ 2^h →
      let P := v.widePlacement h width
      let A := v.privateArena P h width
      let stock := v.fixedTerminalStock P h width
      let _bits := v.wideSignedPage h width stock
      let r := Fintype.card (Slots h D k)
      let decl := declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A)
      let _owners := sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh decl) r P.catalogue.rows
      ∀ size, A.endAddress v.mesh ≤ size → ∀ (π : Equiv.Perm (Fin (2^h))) (raw : Boot.Tape h D),
        let order := wideRouteOrder h D k
        let _m := v.wideSignedMidAt h width size stock v.radius π order raw
        v.wideSignedCheckoutAt h width size stock v.radius π order raw (A.endAddress v.mesh)=0 →
        let final:=v.wideSignedCheckoutAt h width size stock v.radius π order raw
        let f:=v.nativeFormats P h width
        (∀a,Event.attempt a∈events v.mesh→let ar:=(f a).pricedArea
          ∀i : Fin ar.goods,(final (ar.output+ar.goods+ar.goods+i.val)).val≤v.menu.maximum*width) ∧
        ∀b,Event.feed b∈events v.mesh→∀ c∈(FeedLayout.atEvent (N:=CoreBoard.Stages h D)
          v.mesh A f P.joint.initial width v.keepLimit b).columns,∀i:Fin c.rows,
          (final (c.overflow+i.val)).val≤(v.keepLimit+1)*width := by
  filter_upwards [v.readback_run,v.paid_attempt_cells] with h available priced
  intro width small floor budget P A stock size extent π raw order accepted final f
  let _bits := v.wideSignedPage h width stock
  let r := Fintype.card (Slots h D k)
  let decl := declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh P.catalogue P.routes F A)
  let _owners := sinkBank (v.catalystStaticStart P h width) (rowOnlyCount v.mesh decl) r P.catalogue.rows
  let mem := v.wideSignedMidAt h width size stock v.radius π order raw
  obtain ⟨receipt⟩:=available width small floor budget size extent π raw accepted
  let banks:=TerminalLayout.settlement _bits stock
  let src:=TerminalLayout.source _bits
  let tab:=TerminalLayout.table _bits
  let dst:=TerminalLayout.destination _bits
  exact ⟨priced P width r banks src tab dst _owners π mem mem receipt,
    fun b live c hc i=>v.paid_feed_cell P h width r banks src tab dst _owners π mem mem receipt b live c hc i⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
