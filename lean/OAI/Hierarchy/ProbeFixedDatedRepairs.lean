import OAI.Hierarchy.ProbeFixedReadbackRun
import OAI.Hierarchy.ProbeFixedRepairRun
import OAI.Hierarchy.ProbeFixedRepairWordRoom

namespace OAI
/-! # A measured failed ballot is a paid repair on the adjacent physical calendar accounts -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe AdaptiveProbe.OuterBank
open StripChart StockCommit PurchaseCT PurchaseFrozen CatalystArchive
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)

structure RepairWordBounds (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ) : Prop where
  late : v.stripHeight≤z
  threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^(wordBits z (2^v.W) copies)
  alphabet : v.menu.alphabet<2^(wordBits z (2^v.W) copies)
  rate : v.keepLimit*width+v.menu.maximum*v.menu.copiesAt v.copyScale width<2^(wordBits z (2^v.W) copies)
  payloadWord : (v.publicHeader P z width).payload.maxWord<2^(wordBits z (2^v.W) copies)
  boughtWord : (v.publicHeader P z width).bought.maxWord<2^(wordBits z (2^v.W) copies)

include D in
def ReadbackRun.failed_event (B : RepairWordBounds v P z width) (a : Attempt)
    (before later : List Event) (m : Memory W) (cut : Slot C mem (.attempt a) before later m)
    (failed : AttemptGate.actual (repair C a).policy (PurchaseStage.postSnapshot ((C).layout a) (repair C a) (prepared C a m))=2) :
    v.RepairSlot P z width r banks src tab dst owners a m := by
  have present : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events (C).mesh
    rw [cut.events]
    simp
  exact RepairSlot.ofWords v P z width r banks src tab dst owners mem D.nativeStock D.valid D.resident
    D.prices D.charges D.digitBudget B.late B.threshold B.alphabet B.rate D.widths a before later m cut
    (D.boards a present).1 failed

include D in
theorem ReadbackRun.outer_failed (B : RepairWordBounds v P z width) (j h : ℕ)
    (hj : j<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) (failed : observedMode C mem j h=2) :
    Nonempty ((A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin
      (phaseTime v.finish v.mesh.inject j) ((A).trial C mem j h) ((A).inner C mem j h 0 0)) := by
  classical
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  obtain ⟨later,cut⟩:=outer_slot C mem j h hj hh D.nativeStock.mounted_all
  let S:=D.failed_event B (.outer j h) _ later _ cut failed
  let fit:=v.payload_fit_at_slot P z width r banks src tab dst owners j h _ S D.payload
  have raw:=v.payload_repair P z width r banks src tab dst owners j h _ fit S (D.payloadRows ⟨j,hj⟩ ⟨h,hh⟩) B.payloadWord
  rw [←v.phase_clock j]
  exact ⟨raw⟩

include D in
theorem ReadbackRun.inner_failed (B : RepairWordBounds v P z width) (j h u b : ℕ)
    (hj : j<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) (hu : u<v.mesh.reserveSteps)
    (hb : b<v.mesh.innerFuel) (failed : observedInnerMode C mem j h u b=2) :
    Nonempty ((A).bank.FailedRows (2^z) width v.actualK v.keepLimit v.loss v.menu.margin
      (reserveTime v.mesh v.finish j u) ((A).inner C mem j h u b) ((A).inner C mem j h u (b+1))) := by
  classical
  let : Nonempty (Fin k):=⟨⟨0,v.positive⟩⟩
  let date:=Attempt.inner j h u b
  obtain ⟨later,cut⟩:=inner_slot C mem j h u b hj hh hu hb D.nativeStock.mounted_all
  let S:=D.failed_event B date _ later _ cut failed
  let fit:=v.purchased_fit_at_slot P z width r banks src tab dst owners j h u b _ S D.payload
  let geo:=D.boughtRows ⟨j,hj⟩ ⟨h,hh⟩ ⟨u,hu⟩ ⟨b,hb⟩
  have floor:=((D.keys j h).1).trans (show (G).first≤(G).base v.mesh (.attempt date) from Nat.le_add_right ..)
  have raw:=v.purchased_repair P z width r banks src tab dst owners j h u b _ fit S geo B.boughtWord π floor
    (D.purchased ⟨j,hj⟩ ⟨h,hh⟩ ⟨u,hu⟩ ⟨b,hb⟩)
  change Nonempty ((A).bank.FailedRows _ _ _ _ _ _ _ _
    ((A).read (.inner j h u (b+1)) (innerState C mem j h u (b+1))))
  rw [inner_succ]
  exact ⟨raw⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
