import OAI.Hierarchy.DescentProfiledResetArea
import OAI.Hierarchy.DescentTerminalRegisteredSliceFields

namespace OAI
/-! Lookup and row extents at the actual final profiled register position. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook
open DescentPacking.PackedMatch.Local.Stage DescentTerminalFixedSlices DescentTerminalSliceShelf
open Filter
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] {n d:ℕ} {G:PoweredGadget F} {board:NonlinearExpanders.Graph n d}
    {op:RotorSpec} {t f g reset drift degreeMax h:ℕ}
variable (x:ResetArea G board op t f g reset drift degreeMax h)

/-- The last field decoder starts at the actual register cursor, including
any private host-padding and reset ingress there. -/
def slicePhase : Phase F :=
  Phase.atPorts G x.sched board x.k x.frozen x.v.age x.v.p f g drift x.v.degree h
    x.v.menu.ordinary op x.old x.v.position.floor

theorem slice_layout (last:x.v.age+1=x.sched.length) :
    x.slicePhase.output=x.stage.successor ∧ x.slicePhase.dateBase=x.base ∧
    x.slicePhase.output.receiver.blocks=2^x.k ∧ x.slicePhase.output.receiver.hosts=x.sched.hostSize x.sched.length ∧
    x.slicePhase.output.receiver.groups=x.sched.groupCount x.sched.length ∧
    x.slicePhase.output.argumentSlots=x.sched.retainedArgumentsAt G drift :=by
  have actual:=Phase.scheduled_layout G x.sched board x.k x.frozen x.v.age x.v.p f g drift x.v.degree h
    x.v.menu.ordinary op x.old.operandLanes x.old.roleLanes x.old.venue x.old.io.wire x.old.io.roster
    x.inside last
  have gr:x.sched.groupCount x.sched.length=x.sched.baseGroups:=by simp [AtomSchedule.groupCount]
  exact ⟨rfl,rfl,actual.1,actual.2.1,actual.2.2.1.trans gr.symm,actual.2.2.2.2.1⟩

variable (G board op t f g reset drift degreeMax)
local notation "σ" => ResetOutput.receiverRate G board op t f g reset (atRound t)
local notation "α" => 1+operandExponent G (stageNumbers G t 0 f g reset 0 0)

/-- The receiver's underlying venue has the last reset's calendar degree.
The finite coefficient-degree parameter may be different. Both are taken
from the actual profiled position. -/
theorem last_lookup (τ B:ℕ) (branch:G.b≤2^(capRate G t g)) (positive:0<B)
    (purchase:2*(τ+(σ+α))≤B) :
    ∀ᶠ h:ℕ in atTop,∀(v:ProfiledPosition G board op t f g reset τ drift degreeMax B h)
      (cut:v.IsReset),let x:=atCut G board op t f g reset drift degreeMax v cut
      v.age+1=x.sched.length→
        let P:=x.slicePhase
        let L:=2+3*P.output.argumentSlots
        P.digits*L+Nat.clog 2 (L+1)≤h/2 ∧
        DescentTerminalPointerFrame.size L P.digits≤2*2^(h/2) ∧
        P.output.receiver.blocks=2^x.k ∧ P.output.receiver.hosts=x.sched.hostSize x.sched.length :=by
  filter_upwards [named_digits_for G board op t f g reset τ (atRound t) drift B degreeMax branch positive purchase] with h acquired
  rintro v cut
  let x:=atCut G board op t f g reset drift degreeMax v cut
  change v.age+1=x.sched.length→_
  intro last
  have date:=acquired v.sites v.age v.p v.degree v.menu.ordinary x.old.venue x.old.operandLanes
    x.old.roleLanes x.inside x.old.io.wire x.old.io.roster v.grainLimit v.degreeLimit x.reached_degree
    v.geometry.capacity v.geometry.format.paid
  have layout:=x.slice_layout last
  change
    x.slicePhase.digits*(2+3*x.stage.successor.argumentSlots)+Nat.clog 2 (2+3*x.stage.successor.argumentSlots+1)≤h/2 ∧
    DescentTerminalPointerFrame.size (2+3*x.stage.successor.argumentSlots) x.slicePhase.digits≤2*2^(h/2) ∧ _
  have same:x.slicePhase.digits=physicalWidth (x.sched.groupCount x.sched.length) x.stage.successor.nodes
      x.stage.successor.primitive.chart.bits x.stage.successor.nodeBits:=by
    unfold Phase.digits
    rw [layout.2.2.2.2.1]; rfl
  rw [same]
  exact ⟨date.1,date.2,layout.2.2.1,layout.2.2.2.1⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline.ResetArea

end OAI
