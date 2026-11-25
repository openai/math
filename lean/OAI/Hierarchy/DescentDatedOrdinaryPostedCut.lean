import OAI.Hierarchy.DescentRegisteredOrdinaryAdvance
import OAI.Hierarchy.DescentDatedOrdinaryRangeExit

namespace OAI
/-! The actual branch and the numerical post-write snapshot at a selected ordinary ticket. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position) (c : C) (mem : Memory w)

local notation "t" => (traces c)
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


local notation "prog" pos:arg cash:arg => (make DatePorts.ordinaryDate) w (b.profile i) b.header pos cash
local notation "next₀" => (⟨make DatePorts.ordinaryPorts,(v).fullEnd root₀⟩ : Position)
local notation "mv" pos:arg cash:arg => (⟨(prog pos cash),next₀⟩ : Move w)


set_option maxHeartbeats 1000000 in
include before ticket after cut in
omit [Fintype P] in
theorem ordinary_posted_cut (positive : 0<k) (room : (make DatePorts.OrdinaryCodeRoom) w)
    (exec : (make DatePorts.OrdinaryExecutionRoom) w (b.profile i) b.header room)
    (fixed : ∀r : RunTrace.Events traces i, ∀y : Move w, issued traces b i r at₀ y → y = mv positive room) :
    (code) i=(prog positive room) ∧ (calendar (w:=w) traces b initial (i+1)).ports=DatePorts.ordinary (v) ((v).stageStart root₀) ∧
    DateCode.history code mem (i+1)=(make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram :=by
  have posted : issued traces b i (⟨c,evt⟩ : RunTrace.Events traces i) at₀ (mv positive room) := ⟨positive,room,rfl⟩
  obtain ⟨instructionAt,positionAt⟩ := returned traces b initial i _ (mv positive room) posted fixed
  refine ⟨instructionAt,congrArg Position.ports positionAt,?_⟩
  apply DateCode.history_event code mem i (Q:=fun out=>out=(make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram)
  refine ⟨(make DatePorts.ordinaryOutput) w (b.profile i) b.header positive room exec ram,?_,rfl⟩
  rw [instructionAt]
  exact ((make DatePorts.ordinary_output) w (b.profile i) b.header positive room exec ram).1

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
