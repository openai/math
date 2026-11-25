import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # Original static tables at a particular slot of the fixed chronological run -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "A" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "g" => v.stamp P z width r banks src tab dst owners

/-- The mounted slot determines the live occurrence plan and half table from
the static board and origin memory through the complete preceding event list. -/
theorem slot_inputs (init fixture : Memory W)
    (boards : ∀a,Event.attempt a∈events v.mesh →
       TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)) ∧
       Original (f a) (g a) (StripChart.start B a) (A).first init fixture)
    (a : Attempt) (prior tail : List Event) (entry : Memory W)
    (cut : Slot C init (.attempt a) prior tail entry) :
    TrialData C a entry fixture (f a).pricedArea (f a).stockSource (g a) v.keepLimit width
      ((A).base v.mesh (.attempt a)) := by
  have split : events v.mesh=prior++(.attempt a)::tail:=cut.events
  have live : Event.attempt a∈events v.mesh:=by rw [split]; simp
  have idx : position v.mesh (.attempt a)=prior.length:=cut.ordinal
  have part : (events v.mesh).take (position v.mesh (.attempt a))=prior:=by
    rw [idx,split,List.take_left]
  have recorded : state C init (position v.mesh (.attempt a))=entry:=by
    change run C ((events v.mesh).take (position v.mesh (.attempt a))) init=entry
    rw [part]
    exact cut.entry
  obtain ⟨layout,origin⟩:=boards a live
  let feeds:=feedColumns («N»:=N) v.mesh A f P.joint.initial width v.keepLimit
  have floor (e : Event) (u : ℕ) (hu : u<(A).first) : protected C u e ∧ outside C u e:=
    v.event_prefix P z width r banks src tab dst owners e u (hu.trans_le (show (A).first≤(A).base v.mesh e from Nat.le_add_right ..))
  have done : Calendar.mounted C ((events v.mesh).take (position v.mesh (.attempt a))) init:=by
    rw [part]
    exact cut.prefixReady
  have fit : ready C (.attempt a) (state C init (position v.mesh (.attempt a))):=by
    rw [recorded]
    exact cut.currentReady
  have proof := trial_data v.mesh v.finish (v.basePhase width) f feeds
    (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun u=>(StripChart.header F B u).fieldTerm) (StripChart.id F B P.catalogue) a v.keepLimit width (A).first
    ((A).base v.mesh (.attempt a)) (StripChart.start B a) init fixture layout origin floor done fit
  change TrialData C a (state C init (position v.mesh (.attempt a))) fixture (f a).pricedArea
    (f a).stockSource (g a) v.keepLimit width ((A).base v.mesh (.attempt a)) at proof
  rwa [recorded] at proof

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
