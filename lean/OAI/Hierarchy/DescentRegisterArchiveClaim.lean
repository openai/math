import OAI.Hierarchy.DescentArchiveRegisterFlag
import OAI.Hierarchy.DescentReachedArgumentPointer
import OAI.Hierarchy.DescentRegisterArchiveInduction
import OAI.Hierarchy.DescentRegisterArchiveValues
import OAI.Hierarchy.DescentChronologicalBundle
import OAI.Hierarchy.DescentArchivePalette
import OAI.Hierarchy.DescentRegisterArchiveSeedClaim

namespace OAI
/-! # The actual primitive encoding, local node order and operand intervals along a path -/
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

variable {W : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached W G q ε S k i z D wire hist}
    {V : MarkedWorld F d P bits} {j z₁ D₁ : ℕ} {last : Reached V G q ε S k j z₁ D₁ wire hist}
    (before : Path t.first r) (after : Path r last) (pin : P→ℕ)

omit [Fintype P] in
/-- The aligned profile and whole-word witnesses change no cell of a published archive. -/
theorem archiveClaim_at (pos : Position) (mem : Memory w)
    (whole : before.whole p) (aligned : before.aligned p R) (chosen : before.OnlyRotor op) :
    archiveClaim t positive units pins op menu origin order firstShape original pin before pos mem ↔
      let archive:=before.archive p positive origin whole
      let rank:=trajectory p positive origin order before whole
      let schema:=archiveShape positive units pins origin firstShape before whole aligned
      let code:=encodePath op menu before positive whole chosen origin original
      ∃room : DatePorts.RangeRoom pos.ports r archive.bit,
        DatePorts.ArchiveRead pos.ports r archive.bit rank room schema op code.atNode
          (Reached.argumentPointer r archive.bit rank schema positive pin pos.ports.argumentsPerNode)
          (archiveFlag r archive.bit rank pos.ports room) mem :=by
  constructor
  · intro all
    exact all whole aligned chosen
  · intro one _ _ _
    exact one

omit [Fintype P] in
theorem path_witnesses (h₀ : (before.append after).whole p) (h₁ : (before.append after).aligned p R)
    (h₂ : (before.append after).OnlyRotor op) :
    before.whole p ∧ before.aligned p R ∧ before.OnlyRotor op :=by
  induction after with
  | here=>exact ⟨h₀,h₁,h₂⟩
  | ordinary _ _ ih=>exact ih h₀ h₁.1 h₂
  | reset _ _ ih=>exact ih h₀.1 h₁.1 h₂.1

omit [Fintype P] in
theorem archive_on_path (pos : Position) (mem : Memory w)
    (read : archiveClaim t positive units pins op menu origin order firstShape original pin before pos mem)
    (h₀ : (before.append after).whole p) (h₁ : (before.append after).aligned p R)
    (h₂ : (before.append after).OnlyRotor op) :
    ∃(whole : before.whole p) (aligned : before.aligned p R) (chosen : before.OnlyRotor op),
      let archive:=before.archive p positive origin whole
      let rank:=trajectory p positive origin order before whole
      let schema:=archiveShape positive units pins origin firstShape before whole aligned
      let code:=encodePath op menu before positive whole chosen origin original
      ∃room : DatePorts.RangeRoom pos.ports r archive.bit,
        DatePorts.ArchiveRead pos.ports r archive.bit rank room schema op code.atNode
          (Reached.argumentPointer r archive.bit rank schema positive pin pos.ports.argumentsPerNode)
          (archiveFlag r archive.bit rank pos.ports room) mem :=by
  obtain ⟨whole,aligned,chosen⟩:=path_witnesses t op before after h₀ h₁ h₂
  exact ⟨whole,aligned,chosen,read whole aligned chosen⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
