import OAI.Hierarchy.DescentRegisteredResetFits
import OAI.Hierarchy.DescentScheduledPaddedReady

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)


set_option quotPrecheck false
local notation "current" i => calendar (w:=w) traces b initial i
local notation "epochs" => kindCalendar S.rounds S.height
local notation "outer" i => PhysicalReset.scheduledAtPorts G S b.board k b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (current i).ports (current i).floor

private theorem snapshot_epochs_length (t J : ℕ) : (kindCalendar t J).length=(t+1)*J:=by
  induction J with
  | zero=>rfl
  | succ J ih=>
    rw [kindCalendar,List.replicate_succ,List.flatten_cons,List.length_append]
    change (kindPeriod t).length+(kindCalendar t J).length=_
    rw [ih,Nat.mul_succ]
    simp [kindPeriod,Nat.add_comm]

local notation "site₀" j => (current j).ports
local notation "after₀" j => (site₀ j).afterPad k (current j).floor
local notation "padEnd" j => (site₀ j).priorStart k (current j).floor
local notation "room₀" j => PhysicalReset.ScheduledCodeRoom G S b.board k b.tail j b.p b.f b.gain
  b.drift b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0)
  (site₀ j).operandLanes (site₀ j).roleLanes (site₀ j).venue (site₀ j).io (padEnd j) w (after₀ j).archive
omit [Fintype P] in
theorem reset_issued_ready (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ) (e : RunTrace.Events traces i)
    (reset : e.2.isReset=true) (geom : Geometry G S b k w i (current i))
    (short : 8*b.receiverWidth G S k i (current i).ports≤b.payload) (bus : b.payload≤w)
    (degreeRoom : (current i).ports.venue.degree+1<2^w) (top : (outer i).fullEnd<2^w) (res : room₀ i) :
    PhysicalReset.ScheduledReady G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
      b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (site₀ i).operandLanes
      (site₀ i).roleLanes (site₀ i).venue (site₀ i).io (padEnd i) w (after₀ i).archive geom.capacity res :=by
  have stamp := e.2.shown
  rw [tags e.1,reset] at stamp
  have slot:=reset_slot_index S.rounds S.height i stamp
  have within : i<S.length:=by
    rw [List.head?_drop] at stamp
    have lt: i<(epochs).length:=(List.getElem?_eq_some_iff.mp stamp).choose
    simpa only [snapshot_epochs_length,AtomSchedule.length] using lt
  have pitch := geom.format.pitch within
  rw [NativePitch.incoming,ite_eq_left within,ite_eq_left slot] at pitch
  have groups : S.baseGroups=2^b.tail:=by
    obtain ⟨t,r,J,M,eqn⟩:=geom.room.scheduled
    exact congrArg AtomSchedule.baseGroups eqn
  let site:=(current i).ports
  have args : (outer i).inner.successor.setup.retained.previousArgs=site.argumentsPerNode:=geom.arguments.symm
  have phaseShort : 8*(outer i).inner.successor.groupWidth≤b.payload :=
    (Nat.mul_le_mul_left 8 (b.receiverWidth_at G S k i site (site.priorStart k (current i).floor)).le).trans short
  exact scheduled_padded_ready G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) site (current i).floor w
    geom.room.hosts geom.format.width geom.capacity geom.room.population.groups pitch groups geom.room.radix
    within geom.room.header geom.room.wires geom.room.paid phaseShort bus degreeRoom top
    (geom.archive.data (outer i).inner.successor.setup.retained) geom.archive.blocks geom.archive.roles args res

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
