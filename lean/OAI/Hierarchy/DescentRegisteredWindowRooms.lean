import OAI.Hierarchy.DescentDatePortActorRoom
import OAI.Hierarchy.DescentDatePortPortRoom
import OAI.Hierarchy.DescentDatePopulation
import OAI.Hierarchy.DescentDatePortPaidRoom
import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentDatePortPostedHeader
import OAI.Hierarchy.DescentDatePortWireRoom
import OAI.Hierarchy.DescentDateArgumentSlots

namespace OAI
/-! # Bank extents carried by each real register transition -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)

variable {n degree : ℕ} (b : Menu n degree)
set_option quotPrecheck false
structure Rooms (G : PoweredGadget F) (S : AtomSchedule) (b : Menu n degree) (k w i : ℕ) (pos : Position) : Prop where
  archive : DatePorts.ArchiveWidths G S b.op pos.ports k b.tail b.p b.drift b.degreeLimit b.payload i
  wires : pos.ports.WireRoom w pos.floor
  header : pos.ports.HeaderRoom w pos.floor
  args : DatePorts.ArgumentSlots G S pos.ports b.drift
  paid : pos.ports.PaidRoom w pos.floor
  ports : pos.ports.PortRoom w pos.floor
  actors : pos.ports.ActorRoom w pos.floor
  population : DatePorts.Population S pos.ports i
  radix : S.radix=2^k
  initialSites : ∃d,S.initialSites=2^d
  scheduled : ∃ t reset J M,S=stageNumbers G t J b.f b.gain reset M b.tail

theorem Rooms.hosts {i:ℕ} {pos:Position} (room:Rooms G S b k w i pos) :
    pos.ports.venue.hosts=S.hostSize i :=by
  obtain ⟨d,base⟩:=room.initialSites
  exact DatePorts.Population.venue_eq S room.population base room.radix

theorem Rooms.wordBits {i:ℕ} {pos:Position} (room:Rooms G S b k w i pos) : 0<w:=by
  by_contra! zero
  have width : w=0 := Nat.eq_zero_of_le_zero zero
  have count:=room.header.count
  have positive:=count.1
  have size:=count.2.1
  rw [width] at size
  simp only [pow_zero] at size
  omega

/-- Width tested in the finite optimization before selecting the reset pitch. -/
def Menu.receiverWidth (b : Menu n degree) (G : PoweredGadget F) (S : AtomSchedule) (k i : ℕ)
    (ports : DatePorts) : ℕ :=
  let tag:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) b.op
  let earlier:=ResetOutput.Prior.atDate G S i b.p b.drift ports.operandLanes ports.roleLanes tag ports.venue
  let pre:=NativePitch.resetCut S k b.tail b.p b.f b.payload i
  let next:=NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary (i+1)
  (ResetOutput.fromBoard G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload 0 pre 1 next
    b.op.C b.op.w earlier 0).groupWidth

omit [Fintype P] in
/-- The four bounds at the successor follow from the published ordinary or reset
registers and the two scalar bounds of the public allocation. -/
theorem issued_register_room (i : ℕ) (e : RunTrace.Events traces i) (at_ : Position) (step : Move w)
    (posted : issued traces b i e at_ step) (old : Rooms G S b k w i at_)
    (ceiling : step.next.floor<2^w)
    (short : e.2.isReset=true → 8*(b.receiverWidth G S k i at_.ports)≤b.payload) :
    Rooms G S b k w (i+1) step.next :=by
  obtain ⟨t,resetAge,J,M,scheduled⟩:=old.scheduled
  obtain ⟨d₀,firstSites⟩:=old.initialSites
  have live (j:ℕ) : 0<S.hostSize j:=by
    rw [AtomSchedule.hostSize,firstSites,old.radix]
    positivity
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary «prefix» ticket suffix path=>
    obtain ⟨pos,paid,rfl⟩:=posted
    let v:=DatePorts.ordinaryModel at_.ports ticket b.op b.gain b.tail b.p b.f b.drift
      b.degreeLimit b.payload (b.seats i) at_.floor b.ordinary
    let floor:=v.stageStart at_.floor
    exact ⟨DatePorts.ordinary_widths G S b.op at_.ports ticket b.gain b.tail b.p b.f b.drift
        b.degreeLimit b.payload (b.seats i) at_.floor b.ordinary,
      DatePorts.ordinary_wire_room v floor w ceiling,
      DatePorts.ordinary_header_room v floor w ceiling,
      DatePorts.ordinary_argument_slots G S b.op at_.ports ticket b.gain b.tail b.p b.f b.drift
        b.degreeLimit b.payload (b.seats i) at_.floor b.ordinary old.args,
      DatePorts.ordinary_paid_room v floor w ceiling,
      DatePorts.ordinary_port_room v floor w ceiling,
      DatePorts.ordinary_actor_room v floor w ceiling,
      (DatePorts.ordinary_population G S b.op at_.ports ticket b.gain b.tail b.p b.f b.drift b.degreeLimit b.payload
        (b.seats i) at_.floor b.ordinary scheduled (live i) old.radix).1,old.radix,old.initialSites,old.scheduled⟩
  | reset «prefix» B suffix path=>
    obtain ⟨cap,paid,rfl⟩:=posted
    let earlier:=at_.ports.priorStart k at_.floor
    let v:=PhysicalReset.scheduled G S b.board k b.tail i b.p b.f b.gain b.drift
      b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) at_.ports.operandLanes
      at_.ports.roleLanes at_.ports.venue at_.ports.io.wire at_.ports.io.roster earlier
    let inp:=DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
      b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) at_.ports at_.floor w paid
    let pre:=NativePitch.resetCut S k b.tail b.p b.f b.payload i
    let next:=NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary (i+1)
    let tag:=DescentPrimitivePalette.printedBits G (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) b.op
    have fits (t : ℕ) (live : t∈v.successor.receiverUnits) :
        t*v.successor.receiver.lanes≤b.payload/2:=
      PhysicalReset.selected_room G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
        pre next b.op.C b.op.w at_.ports.operandLanes at_.ports.roleLanes tag at_.ports.venue
        at_.ports.io.wire at_.ports.io.roster earlier t (short rfl) (Or.inr live)
    exact ⟨DatePorts.reset_widths G S b.op b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
        b.ordinary at_.ports.operandLanes at_.ports.roleLanes at_.ports.venue at_.ports.io.wire at_.ports.io.roster
        earlier inp fits,
      DatePorts.reset_wire_room v (v.stageStart earlier) inp ceiling,
      DatePorts.reset_header_room v (v.stageStart earlier) inp rfl rfl ceiling,
      DatePorts.reset_argument_slots G S b.op b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
        b.ordinary at_.ports.operandLanes at_.ports.roleLanes at_.ports.venue at_.ports.io.wire at_.ports.io.roster
        earlier inp,
      DatePorts.reset_paid_room v (v.stageStart earlier) inp ceiling,
      DatePorts.reset_port_room v (v.stageStart earlier) inp ceiling,
      DatePorts.reset_actor_room v (v.stageStart earlier) inp ceiling,
      (DatePorts.reset_population G S b.op b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
        b.ordinary at_.ports.operandLanes at_.ports.roleLanes at_.ports.venue at_.ports.io.wire at_.ports.io.roster
        earlier inp (live (i+1))).1,old.radix,old.initialSites,old.scheduled⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
