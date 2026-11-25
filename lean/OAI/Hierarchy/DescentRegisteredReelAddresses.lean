import OAI.Hierarchy.DescentNamedOrdinaryPorts
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentScheduledResetAtPorts
import OAI.Hierarchy.DescentDatedSavedRotation

namespace OAI
/-! # Public addresses of the observed ballot count and saved rotation -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.Menu
open DescentCompiler DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F : Type} [Field F] {bn bd : ℕ} (b : RegisterTimeline.Menu bn bd)
    (G : PoweredGadget F) (S : AtomSchedule) (k i : ℕ) (pos : Position)

def resetFlag (S : AtomSchedule) (i : ℕ) := ((kindCalendar S.rounds S.height).drop i).head?.getD false

def rotationAt : ℕ :=
  if resetFlag S i then
    let a:=PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) pos.ports pos.floor
    (NativeDate.reset (F:=F) (P:=Unit) a.inner).saved a.priorStart
  else
    let stage:=PhysicalOrdinary.StaticCore.profileStart G S b.gain k i b.p b.payload (b.seats i) pos.floor
    let core:=PhysicalOrdinary.StaticCore.atAge G S b.gain k i b.p b.payload (b.seats i) pos.floor pos.ports.io.roster
    core.area.flagEnd pos.ports.io.roster stage+2^k

/-- A reset has no selector row. Its unused count address is the measured matrix slot,
so every address of the public tape lies strictly below the next cursor. -/
def selectorAt : ℕ :=
  if resetFlag S i then b.rotationAt G S k i pos else
    (VenueProgram.Registered.atAge G S b.op b.gain k i b.p b.tail b.f b.drift b.degreeLimit b.payload
      (b.seats i) pos.floor pos.ports b.ordinary).selector G

theorem reset_rotation (tag : ((kindCalendar S.rounds S.height).drop i).head?=some true) :
    let a:=PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) pos.ports pos.floor
    b.rotationAt G S k i pos=(NativeDate.reset (F:=F) (P:=Unit) a.inner).saved a.priorStart:=by
  simp only [rotationAt,resetFlag,tag,Option.getD_some,ite_true]

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.Menu

end OAI
