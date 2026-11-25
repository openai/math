import OAI.Hierarchy.DescentRegisterArchiveSeedClaim

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks
open DescentPrimitivePalette DescentRotor DescentResetGates ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
/-- A stored read at one proof of the range bounds also holds at the supplied proof. -/
theorem archive_read_at_bounds {available : Prop} (read : available → Prop)
    (stored : ∃ room, read room) (room : available) : read room := by
  obtain ⟨_, measured⟩ := stored
  exact measured

variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    (t : RunTrace G q ε S k wire hist final bits d)
    {p R : ℕ} (positive : 0<p) (units : 1≤R) (pins : ∀pin,p∣bits pin)
    (op : RotorSpec) (menu : Runnable F op)
    (origin : Archive t.inputWorld) (order : Local origin.bit)
    (firstShape : WorldShape p R origin.bit)
    (original : Encoding (Label G hist t.firstGrain op) (dictionary G op menu p) origin.bit)

omit [Fintype P] in
/-- Read the retained archive at explicitly supplied geometric bounds. -/
theorem profiled_archive_previous_data
    {U : MarkedWorld F d P bits} {i z D : ℕ} {reached : Reached U G q ε S k i z D wire hist}
    (pin : P → ℕ) (before : Path t.first reached) (pos : Position) (mem : Memory w)
    (whole : before.whole p) (aligned : before.aligned p R) (chosen : before.OnlyRotor op)
    (bounds : DatePorts.RangeRoom pos.ports reached (before.archive p positive origin whole).bit)
    (previous : archiveClaim t positive units pins op menu origin order firstShape original pin before pos mem) :
    let archive:=before.archive p positive origin whole
    let rank:=trajectory p positive origin order before whole
    let schema:=archiveShape positive units pins origin firstShape before whole aligned
    let code:=encodePath op menu before positive whole chosen origin original
    DatePorts.ArchiveRead pos.ports reached archive.bit rank bounds schema op code.atNode
        (Reached.argumentPointer reached archive.bit rank schema positive pin pos.ports.argumentsPerNode)
        (archiveFlag reached archive.bit rank pos.ports bounds) mem := by
  exact archive_read_at_bounds _ (previous whole aligned chosen) bounds

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
