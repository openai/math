import OAI.Hierarchy.DescentResetPriorHostPad
import OAI.Hierarchy.DescentPriorNodePresenceShape
import OAI.Hierarchy.DescentScheduledResetChart

namespace OAI
/-! # A reset started from the actual height of the preceding two archives -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentResetPriorHostPad

def resetPad (v : DatePorts) (k : ℕ) : Shape :=
  ⟨v.operandHosts,v.venue.hosts,v.venue.groups,2^k,v.argumentsPerNode,v.operandLanes,v.roleLanes⟩

def presence (v : DatePorts) (k : ℕ) : DescentPriorNodePresence.Chart :=
  ⟨2^k,v.nodes,v.venue.hosts,v.venue.groups,v.tokenBits,v.operandBits,v.roleLanes,v.operandLanes⟩

def priorStart (v : DatePorts) (k floor : ℕ) :=
  (v.presence k).endAddress ((v.resetPad k).endAddress floor)

def afterPad (v : DatePorts) (k floor : ℕ) : DatePorts :=
  let history := (v.resetPad k).history floor v.archive
  {v with
    archive := {history with nodeBase := (v.presence k).out ((v.resetPad k).endAddress floor)}
    operandHosts := v.venue.hosts}

end Hierarchy.DescentSixParty.Chronology.DatePorts

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage ProtocolRAM
noncomputable section

structure AtPorts where
  pad : DescentResetPriorHostPad.Shape
  presence : DescentPriorNodePresence.Chart
  floor : ℕ
  inner : PhysicalReset

namespace AtPorts
def priorStart (a : AtPorts) :=a.presence.endAddress (a.pad.endAddress a.floor)
def fullEnd (a : AtPorts) :=a.inner.fullEnd a.priorStart
theorem stages (a : AtPorts) : a.floor≤a.priorStart ∧ a.priorStart≤a.fullEnd :=
  by
    have h:=a.inner.occupied (a.inner.stageStart a.priorStart)
    exact ⟨((a.pad.cuts a.floor).1.trans (a.pad.cuts a.floor).2).trans (a.presence.lower _),
      (a.inner.ingress.after _).trans ((h.1.trans h.2.1).trans h.2.2)⟩
end AtPorts

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec)
    (s Z : ℕ) (ports : Chronology.DatePorts)

def scheduledAtPorts (floor : ℕ) : AtPorts :=
  ⟨ports.resetPad k,ports.presence k,floor,scheduled G S board k tail age p f gain drift degree h ordinary op s Z
    ports.operandLanes ports.roleLanes ports.venue ports.io.wire ports.io.roster (ports.priorStart k floor)⟩

theorem scheduled_at_ports (floor : ℕ) :
    let a:=scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    a.priorStart=ports.priorStart k floor ∧
    a.fullEnd=a.inner.fullEnd (ports.priorStart k floor) :=⟨rfl,rfl⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
