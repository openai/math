import OAI.Hierarchy.DescentCalendarAbsoluteNumbers
import OAI.Hierarchy.DescentOriginalResetBounds
import OAI.Hierarchy.DescentScheduledEntranceRoom

namespace OAI
/-! The register, archive and lookup inequalities attained at one physical reset. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
open DescentSixParty.PackedFlow.Canvas DescentPackedFlowPublication
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (D f g C packet : ℕ)
set_option quotPrecheck false
local notation "out_" z:arg => (z : Sample).output G board D f g C packet

/-- These are numerical tests on actual inputs and previously purchased words. -/
structure AreaPoint (h : ℕ) (z : Sample) (old : Prior) (a : PhysicalReset) (floor : ℕ) : Prop where
  layout : a.successor=out_ z
  payload : a.payload=h
  localNumbers : ∀m∈z.localNumbers G board D f g C packet,m≤2^h
  fibres : (out_ z).setup.retained.donors=2^z.k
  installed : ∀b,b∈(out_ z).rootUnits ∨ b∈(out_ z).receiverUnits→b*(out_ z).receiver.lanes≤h/2
  selected : 8*(out_ z).groupWidth≤h
  cuts : z.root≤z.previous ∧ z.previous≤(z.sched.groupWidth z.k z.tail z.age)
  next : z.root≤z.sched.groupWidth z.k z.tail (z.age+1)
  matrix : (((z.sched.groupWidth z.k z.tail z.age))+z.k)*(((z.sched.groupWidth z.k z.tail z.age))+z.k)≤h/2
  oldHost : z.sched.hostSize z.age≤2^(3*h)
  newHost : z.sched.hostSize (z.age+1)≤2^(3*h)
  mask : z.nextLanes≤h
  previousKey : (out_ z).middle.signedBits*2^z.previous≤h/2
  previousWords : DescentSignedCableCodec.width D old.venue.cap*old.venue.lanes≤h/2 ∧
    old.venue.paidBits*old.venue.lanes≤h/2
  paid : z.sched.censusBits z.p*old.venue.lanes≤h/2 ∧ old.venue.lanes≤h
  oldCaps : old.nodes≤z.sched.retainedNodes ∧ old.arguments≤z.sched.retainedArgumentsAt G z.drift
  operandLanes : old.operandLanes≤h
  roleLanes : old.primitiveLanes≤h
  archive : (out_ z).setup.retained.wholeWord*old.operandLanes≤h/2 ∧
    (out_ z).roleTransfer.transfer.wholeWord*old.primitiveLanes≤h/2
  book : Book.width a.bits (2^a.k) a.short*a.lanes≤a.payload
  reblock : a.re+a.field*(2^a.re*2^a.e)≤a.payload/2
  packed : let q:=(a.chart (a.stageStart floor)).geo;8*q.bits≤h/2
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
