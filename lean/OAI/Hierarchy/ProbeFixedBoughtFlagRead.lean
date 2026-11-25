import OAI.Hierarchy.ProbeFixedPaidPortData
import OAI.Hierarchy.ProbeFixedPurchaseEntry
import OAI.Hierarchy.ProtocolRAMBoughtTerminal

namespace OAI
/-! # The chronological purchase decision words at the signed checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe PurchaseFrozen
open CatalogueRows BoughtSockets StripDirectory StripChart
open scoped Classical Fin.CommRing

private theorem checkout_before_flag {w q d : ℕ} (chart : Chart w q d) (mesh : Mesh)
    (same : chart.mesh = mesh) (m : Memory w) (flag addr : ℕ) (before : addr < flag) :
    checkedOut chart flag m addr = run chart (events mesh) m addr := by
  subst mesh
  exact ProtocolRAMGeneratedWrite.frame_image flag 1 (historyFlag chart (events chart.mesh))
    (run chart (events chart.mesh) m) addr (.inl before)

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "W" => wordBits z (2^v.W) copies
local notation "B" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
variable (initial : Memory (wordBits z (2^v.W) copies)) (phase : Fin (v.mesh.inject+v.mesh.cool))
    (trial : Fin v.mesh.outerFuel)
local notation "ev" => Attempt.outer phase.val trial.val
local notation "market" => v.frozenMarket P z width phase.val trial.val
local notation "frozen" => v.frozenInput P z width r banks src tab dst owners initial phase.val trial.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem checkout_flags
    (whole : Calendar.mounted (w:=wordBits z (2^v.W) copies)
      (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) initial)
    (archive : ArchiveRoom (w:=wordBits z (2^v.W) copies)
      (v.nativeChart P z width r banks src tab dst owners) initial (v.mesh.inject+v.mesh.cool)) :
    (market).flags+(market).rows<2^W ∧
    ∀j : Fin (market).rows,checkedOut C ((A).endAddress v.mesh) initial ((repair C ev).purchaseOut+j.val)=
      if observedMode C initial phase trial=3 then
        (market).shelf.result (z:=z) (d:=2^v.W) v.sampler k v.depth frozen ((market).flags+j.val) else 0 := by
  have meshEq : (C).mesh = v.mesh := rfl
  have mountedAt : Calendar.mounted (w:=W) C (events (C).mesh) initial :=
    (congrArg (fun mesh : Mesh => Calendar.mounted (w:=W) C (events mesh) initial) meshEq).mpr whole
  have hp : phase.val < (C).mesh.inject + (C).mesh.cool :=
    (congrArg (fun mesh : Mesh => phase.val < mesh.inject + mesh.cool) meshEq).mpr phase.isLt
  have ht : trial.val < (C).mesh.outerFuel :=
    (congrArg (fun mesh : Mesh => trial.val < mesh.outerFuel) meshEq).mpr trial.isLt
  have ready : (market).ready ((guard C ev).apply (trialState C initial phase trial)) :=
    (@outer_head_ready W _ _ C initial mountedAt phase.val trial.val hp ht).2.1
  refine ⟨ready.2.2.2.1,?_⟩
  let rc : (repair C ev).purchaseOut+(market).rows ≤ (A).base v.mesh (.attempt ev)+(A).stride :=
    (f ev).chargeColumns.2.2.1.trans (v.attempt_room P z width ev)
  have saved := priced_flag_terminal (z:=z) (d:=2^v.W) (k:=k) (N:=Stages z (2^v.W))
    v.mesh v.finish (v.basePhase width) A f P.joint.initial
    width v.keepLimit (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun t=>(StripChart.header F B t).fieldTerm) (StripChart.id F B P.catalogue)
    (v.stock_order P z width) initial phase trial phase.isLt trial.isLt whole archive
    (v.purchase_format P z width phase.val trial.val).1 rc
  obtain ⟨_,slot⟩ := outer_slot C initial phase trial hp ht mountedAt
  have member : Event.attempt ev ∈ events (C).mesh := by rw [slot.events]; simp
  have dated : Event.attempt ev ∈ events v.mesh :=
    (congrArg (fun mesh : Mesh => Event.attempt ev ∈ events mesh) meshEq).mp member
  intro j
  have before : (repair C ev).purchaseOut+j.val < (A).endAddress v.mesh :=
    (Nat.add_lt_add_left j.isLt _).trans_le (rc.trans ((A).within v.mesh _ dated))
  exact (checkout_before_flag C v.mesh meshEq initial _ _ before).trans (saved j)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
