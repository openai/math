import OAI.Hierarchy.DescentRegisteredOrdinaryExecution
import OAI.Hierarchy.DescentRegisterCutInduction

namespace OAI
/-! Positive ordinary transitions on the physically executed public branch. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position) (c : C) (mem : Memory w)
    (limit : ℕ) (valid : Prop)
local notation "code" => instruction (w:=w) traces b initial
variable {i z D z' D' : ℕ} {u : ℝ} {W : MarkedWorld F d P bits}
    {src : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {nrm : Normalize ((T.result he).state choice)}
    {dst : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
    (before : Path (traces c).first src) (ticket : OrdinaryLink src he T choice nrm dst)
    (after : Path dst (traces c).last) (cut : (before.ordinary ticket).append after=(traces c).path)
local notation "evt" => (Path.Event.ordinary before ticket after cut)
local notation "at₀" => (calendar (w:=w) traces b initial i)
local notation "ports" => (at₀).ports
local notation "root₀" => (at₀).floor
local notation "ram" => DateCode.history code mem i
local notation "make" f:arg => f ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
    (b.seats i) root₀ b.ordinary
local notation "v" => make DatePorts.ordinaryModel

omit [Fintype P] in
/-- The ordinary move runs on the actual common instruction history, including
the case where a later ballot is the first one rejected. -/
theorem ordinary_advances (positive:0<k) (room:(make DatePorts.OrdinaryCodeRoom) w)
    (exec:(make DatePorts.OrdinaryExecutionRoom) w (b.profile i) b.header room)
    (success:(ports).held src root₀ ram → (before.selections.length+1<limit ∨ valid) →
      (make DatePorts.ordinaryPorts).held dst ((v).fullEnd root₀)
        ((make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram)) :
    advances traces b initial c mem limit valid i evt :=by
  intro prior needed
  let native:=(make DatePorts.ordinaryDate) w (b.profile i) b.header positive room
  let checked:=(make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram
  exact ⟨⟨native,make DatePorts.ordinaryPorts,(v).fullEnd root₀⟩,⟨positive,room,rfl⟩,checked,
    ((make DatePorts.ordinary_output) w (b.profile i) b.header positive room exec ram).1,success prior needed⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
