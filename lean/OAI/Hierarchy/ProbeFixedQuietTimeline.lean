import OAI.Hierarchy.ProbeFixedQuietCash
import OAI.Hierarchy.ProbeFixedQuietFeed
import OAI.Hierarchy.ProbeFixedQuietInputs

namespace OAI
/-! # The quiet intervals of the actual chronological billed register machine -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StockCommit StripChart PurchaseStage
open ThreeFlat.RAM
open private same_inventory from OAI.Hierarchy.ProbeFixedQuietFeed
open scoped Classical BigOperators Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
variable (mem fixture : Memory (wordBits z (2^v.W) copies))
  (boards : ∀a,Event.attempt a∈events v.mesh →
    StockBound.TrialLayout (v.nativeChart P z width r banks src tab dst owners) a
      (v.nativeFormats P z width a).pricedArea (v.nativeFormats P z width a).stockSource
      (v.stamp P z width r banks src tab dst owners a) v.keepLimit width
      ((v.privateArena P z width).base v.mesh (.attempt a)) ∧
    StockBound.Original (v.nativeFormats P z width a) (v.stamp P z width r banks src tab dst owners a)
      (StripChart.start (v.nativeBoards P z width) a) (v.privateArena P z width).first mem fixture)
  (stock : StockBound.Run (v.nativeChart P z width r banks src tab dst owners) (v.stockBanks P z width)
    mem z (CoreBoard.Stages z (2^v.W)) k (v.keepLimit*width))

include boards in
/-- A dormant or successful test advances the clock, and the paid and
inventory columns at the two physical clock positions have exactly equal values. -/
theorem quiet_slot (positive : 0<width) (a : Attempt) (prior tail : List Event) (entry : Memory W)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (mode : AttemptGate.actual (repair C a).policy (postSnapshot ((C).layout a) (repair C a) (prepared C a entry))<2) :
    let idx:=Succession v.mesh (.attempt a)
    (A).read idx.2 (after C (.attempt a) entry)=(A).read idx.1 entry := by
  have inputs:=v.slot_inputs P z width r banks src tab dst owners mem fixture boards a prior tail entry cut
  obtain ⟨ports⟩:=inputs.ports
  have scheduled : Event.attempt a∈events v.mesh:=by
    change Event.attempt a ∈ events (C).mesh
    rw [cut.events]
    simp
  have bits:=v.quiet_stock P z width r banks src tab dst owners a entry scheduled cut.currentReady inputs.toTrialLayout ports mode
  have cash:=v.quiet_paid P z width r banks src tab dst owners a entry scheduled cut.currentReady positive inputs.toTrialLayout ports mode
  intro idx
  apply same_inventory
  · intro i
    exact congrFun bits i
  · exact cash

include boards stock in
/-- The observed outer modes zero and one leave precisely the prior account
in the first physical reserve slot, even when the marked path scan was nonempty. -/
theorem quiet_head (positive : 0<width) (p h : ℕ) (hp : p<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel)
    (mode : observedMode C mem p h=0 ∨ observedMode C mem p h=1) :
    ((A).inner C mem p h 0 0).bits=((A).trial C mem p h).bits ∧
      ((A).inner C mem p h 0 0).paid≤((A).trial C mem p h).paid := by
  obtain ⟨tail,cut⟩:=outer_slot C mem p h hp hh stock.mounted_all
  have quiet : observedMode C mem p h<2 := by omega
  have same : (A).inner C mem p h 0 0=(A).trial C mem p h :=
    v.quiet_slot P z width r banks src tab dst owners mem fixture boards positive (.outer p h) _ tail _ cut quiet
  exact ⟨congrArg Inventory.bits same,(congrArg Inventory.paid same).le⟩

include boards stock in
/-- The actual histogram and stock RAM execution gives all three quiet-calendar
identities, including the last reserve feed and its alias in the outer timeline. -/
theorem quiet_timeline (positive : 0<width)
    (initialRoom : P.joint.initial+PurchaseInventory.footprint z N k+
      (sliceROM (P.joint.initial+PurchaseInventory.footprint z N k) v.mesh.reserveSteps (v.keepLimit*width+1)).size ≤ (G).first)
    (addressRoom : (G).endAddress v.mesh < 2^W) (budget : v.keepLimit*width < 2^W) :
    QuietCalendar A C mem := by
  constructor
  · intro p hp h hh j hj b hb _idle mode
    obtain ⟨tail,cut⟩:=inner_slot C mem p h j b hp hh hj hb stock.mounted_all
    have quiet : observedInnerMode C mem p h j b<2 := by omega
    have step:=v.quiet_slot P z width r banks src tab dst owners mem fixture boards positive
      (.inner p h j b) _ tail _ cut quiet
    change (A).read (.inner p h j (b+1)) (innerState C mem p h j (b+1))=_
    rw [inner_succ]
    exact step
  · intro p hp h hh j hj idle
    obtain ⟨_,cut⟩:=outer_slot C mem p h hp hh stock.mounted_all
    have occurs : Event.attempt (.outer p h)∈events v.mesh:=by
      change Event.attempt (.outer p h) ∈ events (C).mesh
      rw [cut.events]
      simp
    exact v.quiet_feed_local P z width r banks src tab dst owners mem stock initialRoom addressRoom budget
      p h j hp hh hj (boards _ occurs).1 idle
  · intro p _ h _
    exact (nativeAccounts_outer_next C G f P.joint.initial width (v.issued P z width r banks src tab dst owners)
      _ v.a v.radius (probeBonus v.W) _ mem p h).symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
