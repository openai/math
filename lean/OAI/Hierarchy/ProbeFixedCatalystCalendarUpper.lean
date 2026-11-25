import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCatalystCalendarUpper

namespace OAI
/-! # Actual fixed chart retains upper physical private input cells -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width : ℕ)
local notation "A" => v.privateArena P z width

theorem catalyst_calendar_upper (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ)
    (owners : Bank) (m : PurchaseFrozen.Shelf.Mem z (2^v.W)) (x : ℕ) (high : (A).endAddress v.mesh<x)
    (live : Calendar.mounted (v.nativeChart P z width r banks src tab dst owners) (events v.mesh) m) :
    checkedOut (v.nativeChart P z width r banks src tab dst owners) ((A).endAddress v.mesh) m x=m x :=
  priced_calendar_upper (N:=Stages z (2^v.W)) v.mesh v.finish (v.basePhase width) A
    (v.nativeFormats P z width) P.joint.initial width v.keepLimit (P.catalogue.sink r banks src tab dst owners)
    P.catalogue.idBase (fun a=>(StripChart.header F (v.nativeBoards P z width) a).fieldTerm)
    (StripChart.id F (v.nativeBoards P z width) P.catalogue)
    (fun a _=>v.attempt_room P z width a) (v.feed_room P z width) m x ((A).endAddress v.mesh) high.le high live

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
