import OAI.Hierarchy.DescentRegisterPrefixClaim
import OAI.Hierarchy.DescentArchiveRegisterFlag
import OAI.Hierarchy.DescentOriginalArgumentPointer
import OAI.Hierarchy.DescentChronologicalBundle
import OAI.Hierarchy.DescentArchivePalette
import OAI.Hierarchy.DescentReachedLocalNodes

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentOperandStateBanks
open DescentPrimitivePalette DescentRotor DescentResetGates ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}
    (t : RunTrace G q ε S k wire hist final bits d)
    {p R : ℕ} (positive : 0<p) (units : 1≤R) (pins : ∀pin,p∣bits pin)
    (op : RotorSpec) (menu : Runnable F op)
    (origin : Archive t.inputWorld) (order : Local origin.bit)
    (firstShape : WorldShape p R origin.bit)
    (original : Encoding (Label G hist t.firstGrain op) (dictionary G op menu p) origin.bit)

def archiveClaim (pin : P→ℕ) : PrefixClaim t w :=
  fun {_} {_} {_} {_} {reached} before pos mem=>∀(whole : before.whole p) (aligned : before.aligned p R) (chosen : before.OnlyRotor op),
    let archive:=before.archive p positive origin whole
    let rank:=trajectory p positive origin order before whole
    let schema:=archiveShape positive units pins origin firstShape before whole aligned
    let code:=encodePath op menu before positive whole chosen origin original
    ∃room : DatePorts.RangeRoom pos.ports reached archive.bit,
      DatePorts.ArchiveRead pos.ports reached archive.bit rank room schema op code.atNode
        (Reached.argumentPointer reached archive.bit rank schema positive pin pos.ports.argumentsPerNode)
        (archiveFlag reached archive.bit rank pos.ports room) mem

omit [Fintype P] in
theorem archiveClaim_here (pos : Position) (mem : Memory w) (pin : P→ℕ)
    (room : DatePorts.RangeRoom pos.ports t.first origin.bit)
    (seed : DatePorts.ArchiveRead pos.ports t.first origin.bit order room firstShape op original.atNode
      (Reached.argumentPointer t.first origin.bit order firstShape positive pin pos.ports.argumentsPerNode)
      (archiveFlag t.first origin.bit order pos.ports room) mem) :
    archiveClaim t positive units pins op menu origin order firstShape original pin Path.here pos mem :=by
  intro _ _ _
  exact ⟨room,seed⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
