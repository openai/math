import OAI.Hierarchy.TaggedWireFundedCursorReplay
import OAI.Hierarchy.TaggedWideCursorPlacement

namespace OAI
/-! # Every numbered point of a signed history recovers the original funded execution -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard Tagged WireTelescope CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width size : ℕ) (π : Equiv.Perm (Fin (2^h))) (seed : Boot.Tape h (2^v.W))
  (age : v.wideStockHeight≤h) (budget : v.keepLimit*width+1≤2^h) (small : width≤2^h)
set_option quotPrecheck false
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "L" => (v.wideSelector h width age budget small).format.windows
local notation "slot" => (v.wideSelector h width age budget small).format.slot
local notation "base" => v.wideOrigin h width size seed π
local notation "es" => events v.mesh
local notation "orig" => Path slot es base
local notation "curr" => v.wideCursorWidth h width size π seed age budget small
local notation "C" => v.wideSignedChart h width (v.fixedTerminalStock P h width)
local notation "boot" j:arg => v.wideOrigin h width size ((L).header es (encode slot es base j) seed) π

set_option maxHeartbeats 1600000 in
theorem wide_funded_boundary (extent : (A).endAddress v.mesh≤ size) (late : v.cursorReplayHeight≤h)
    (j : orig) (t : Fin ((es).length+1)) :
    Prefix.atWidth («slot» := slot) (events := es) (x₀ := base) (S := siteLast h (2^v.W) k+1)
      (fun {_ _} path => curr path) (Prefix.boundaryIndex j t)=
      v.wireAt h width v.maxBits π.symm t.val (StockBound.state C (boot j) t.val) := by
  let now:=Prefix.boundaryIndex j t
  obtain ⟨rest,back⟩:=Prefix.boundary_suffix j t
  have law:=v.wide_cursor_replay h width size extent π seed age budget small now.path rest late
  have length : (es).length-now.todo.length=t.val:=(Prefix.start_boundary j t).1
  change curr now.path=v.wireAt h width v.maxBits π.symm t.val (StockBound.state C (boot j) t.val)
  exact law.trans (congrArg₂
    (fun (time : ℕ) (path : orig) =>
      v.wireAt h width v.maxBits π.symm time (StockBound.state C (boot path) time)) length back)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
