import OAI.Hierarchy.ProbeFixedCompleteRepair
import OAI.Hierarchy.ProbeFixedRepairFits
import OAI.Hierarchy.ProbeFixedGlobalRun
import OAI.Hierarchy.ProbeFixedModeLifetimes
import OAI.Hierarchy.ProbeFixedReplayPurchase
import OAI.Hierarchy.ProbeFixedQuietTimeline
import OAI.Hierarchy.ProbeFixedPurchaseActivation

namespace OAI
/-! # Original public memory, native stock and chronological incidence rows for the signed calendar -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit CatalystArchive PurchaseFrozen StripDirectory PurchaseCT
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "freq" => DeadlineROM.prices v.mesh v.finish (v.basePhase width)
local notation "fees" => StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
local notation "digits" => v.keepLimit*width+1
local notation "table" => sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps digits
variable (π : Equiv.Perm (Fin (2^z))) (mem fixture : Memory (wordBits z (2^v.W) copies))

/-- Each row refers to the preceding real event list and native frozen memory.
The stock receipts supply the control program's own incoming and published words. -/
structure ReadbackRun where
  nativeStock : StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width)
  valid : admissible C (events v.mesh) mem
  resident : (H).Resident mem
  prices : InitialPrices P.joint z N k freq (fun _=>0) mem
  charges : (fees).Resident mem
  steps : P.joint.steps=v.mesh.reserveSteps
  precision : P.joint.precision=v.precision
  digitBudget : P.joint.cap*P.joint.width=v.keepLimit*width
  payload : width≤2^z
  widths : v.widthFloor≤width
  stride : digits≤2^z
  dimension : 2*v.keepLimit+2≤2^z
  endFits : (G).endAddress v.mesh<2^W
  heap : heapEnd z (2^v.W) copies≤(G).first
  geometry : Shelf.Geometry π mem
  keys : ∀p h, let t:=stratumHeader z (2^v.W) k v.sampler.degree v.depth ((B).stratumHeader p h)
    t.stop≤(G).first ∧ t.Loaded mem
  slices : ∃original : Memory W,∀x,(table).base≤x→x<(table).base+v.mesh.reserveSteps*digits→
    mem x=feedAdvice table v.mesh.reserveSteps digits original x
  boards : ∀a,Event.attempt a∈events v.mesh →
    StockBound.TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((G).base v.mesh (.attempt a)) ∧
    StockBound.Original (f a) (g a) (StripChart.start B a) (G).first mem fixture
  payloadRows : ∀p : Fin (v.mesh.inject+v.mesh.cool),∀h : Fin v.mesh.outerFuel,
    v.PayloadRepairGeometry P z width r banks src tab dst owners p h (trialState C mem p h)
  boughtRows : ∀p : Fin (v.mesh.inject+v.mesh.cool),∀h : Fin v.mesh.outerFuel,
    ∀j : Fin v.mesh.reserveSteps,∀b : Fin v.mesh.innerFuel,
    v.PurchasedRepairGeometry P z width r banks src tab dst owners p h j b (innerState C mem p h j b)
  purchased : ∀p : Fin (v.mesh.inject+v.mesh.cool),∀h : Fin v.mesh.outerFuel,
    ∀j : Fin v.mesh.reserveSteps,∀b : Fin v.mesh.innerFuel,
    PurchasedBirth ((B).outer p h).market.shelf (B).sampler π v.depth ((B).stratumHeader p h) (innerState C mem p h j b) k

variable {v P z width r banks src tab dst owners π mem fixture}
variable (run : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)

include run in
theorem ReadbackRun.archives : ArchiveRoom C mem (v.mesh.inject+v.mesh.cool) :=
  v.mode_archive P z width r banks src tab dst owners mem run.nativeStock (fun a h=>(run.boards a h).1)

include run in
theorem ReadbackRun.positive : 0<width :=
  v.clock.inject_pos.trans_le (v.clock.inject_width.trans run.widths)

include run in
theorem ReadbackRun.inner_skipped (p h j b : ℕ) (hp : p<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel)
    (hj : j<v.mesh.reserveSteps) (hb : b<v.mesh.innerFuel) (idle : observedInnerMode C mem p h j b≠2) :
    (A).inner C mem p h j (b+1)=(A).inner C mem p h j b := by
  let a:=Attempt.inner p h j b
  let now:=innerState C mem p h j b
  let snap:=PurchaseStage.postSnapshot ((C).layout a) (repair C a) (prepared C a now)
  obtain ⟨tail,cut⟩:=inner_slot C mem p h j b hp hh hj hb run.nativeStock.mounted_all
  have noPurchase:=AttemptGate.reserve_no_purchase (repair C a).policy snap rfl
  have range:=AttemptGate.actual_lt (repair C a).policy snap
  change AttemptGate.actual (repair C a).policy snap≠2 at idle
  have low : AttemptGate.actual (repair C a).policy snap<2 := by omega
  have receipt:=v.quiet_slot P z width r banks src tab dst owners mem fixture run.boards run.positive
    a _ tail now cut low
  change (A).read (.inner p h j (b+1)) (innerState C mem p h j (b+1))=_
  rw [inner_succ]
  exact receipt

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
