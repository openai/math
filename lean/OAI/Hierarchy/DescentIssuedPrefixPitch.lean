import OAI.Hierarchy.DescentRegisteredPrefixRooms
import OAI.Hierarchy.DescentDatePortArchivePitchRoom

namespace OAI
/-! # Both original operand pitches on the actual returned register at a chronological cut -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
variable {n degree : ℕ} (b : Menu n degree) (initial : Position)
set_option quotPrecheck false
local notation "model" i:arg a:arg t:arg => DatePorts.ordinaryModel (a:Position).ports t b.op b.gain b.tail b.p b.f b.drift
  b.degreeLimit b.payload (b.seats i) (a:Position).floor b.ordinary
local notation "resetModel" i:arg a:arg => PhysicalReset.scheduled G S b.board k b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (a:Position).ports.operandLanes (a:Position).ports.roleLanes
  (a:Position).ports.venue (a:Position).ports.io.wire (a:Position).ports.io.roster ((a:Position).ports.priorStart k (a:Position).floor)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial

/-- The real ordinary date keeps its cropped argument bus and its separately purchased role bus.
The reset writes both sectors at the chosen receiver pitch. -/
def OutputPitches (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (args roles : ℕ) : Prop :=by
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary before ticket after path =>
    let v:=model i a ticket
    exact b.payload≤v.resolver.lanes*args ∧ b.payload≤v.palette.nextLanes*roles
  | reset before closed after path =>
    let L:=(resetModel i a).successor.receiver.lanes
    exact S.groupCount (i+1)≤L ∨ b.payload≤L*min args roles

omit [Fintype P] in
theorem OutputPitches.weaken {i : ℕ} {e : RunTrace.Events traces i} {at_ : Position} {a r x y : ℕ}
    (fund : OutputPitches traces b i e at_ a r) (args : a≤x) (roles : r≤y) :
    OutputPitches traces b i e at_ x y :=by
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary prev ticket tail cut =>
    exact ⟨fund.1.trans (Nat.mul_le_mul_left _ args),fund.2.trans (Nat.mul_le_mul_left _ roles)⟩
  | reset prev closed tail cut =>
    exact fund.imp_right (fun h=>h.trans (Nat.mul_le_mul_left _ (min_le_min args roles)))

omit [Fintype P] in
theorem issued_output_pitch (i : ℕ) (e : RunTrace.Events traces i) (at_ : Position) (m : Move w)
    (posted : steps i e at_ m) (args roles : ℕ) (numbers : OutputPitches traces b i e at_ args roles) :
    m.next.ports.ArchiveDensity (S.groupCount (i+1)) b.payload args roles :=by
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary before ticket after path =>
    obtain ⟨positive,room,rfl⟩:=posted
    exact DatePorts.ordinary_density (model i at_ ticket) _ _ _ _ _ numbers.1 numbers.2
  | reset before closed after path =>
    obtain ⟨cap,space,rfl⟩:=posted
    let v:=resetModel i at_
    let data:=DatePorts.resetInputs G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
      b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) at_.ports at_.floor w space
    exact (DatePorts.reset_density v _ data _ _ _ numbers rfl).weaken (min_le_left ..) (min_le_right ..)

variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (start : Rooms G S b k w 0 initial)
variable (installed : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (calendar (w:=w) traces b initial i)→
  ∃move : Move w,issued (w:=w) traces b i e (calendar (w:=w) traces b initial i) move ∧ move.next.floor<2^w ∧
    (e.2.isReset=true→8*b.receiverWidth G S k i (calendar (w:=w) traces b initial i).ports ≤ b.payload))
variable (args roles : ℕ)
variable (seed : initial.ports.ArchiveDensity (S.groupCount 0) b.payload args roles)
variable (numbers : ∀i (e : RunTrace.Events traces i),Rooms G S b k w i (calendar (w:=w) traces b initial i) →
  OutputPitches traces b i e (calendar (w:=w) traces b initial i) args roles)

include fixed installed numbers in
omit [Fintype P] in
theorem returned_pitch (i : ℕ) (e : RunTrace.Events traces i) (old : Rooms G S b k w i (cursor i))
    (payload : 0<b.payload) (groups : 0<S.groupCount (i+1)) :
    (cursor (i+1)).ports.ArchivePitchRoom (S.groupCount (i+1)) b.payload args roles :=by
  obtain ⟨m,posted,roof,short⟩:=installed i e old
  have same:=(returned traces b initial i e m posted (fun a z h=>fixed i a e z m h posted)).2
  have shape:=issued_register_room traces b i e _ m posted old roof short
  rw [same]
  exact (issued_output_pitch traces b i e _ m posted args roles (numbers i e old)).pitch_room
    shape.archive payload groups

variable (c : C)
local notation "t" => traces c

include fixed start installed seed numbers in
omit [Fintype P] in
theorem issued_prefix_pitch {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path)
    (payload : 0<b.payload) (groups : ∀j,0<S.groupCount j) :
    (cursor i).ports.ArchivePitchRoom (S.groupCount i) b.payload args roles :=by
  cases p with
  | here=>exact seed.pitch_room start.archive payload (groups 0)
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst ticket =>
    have prior:=rooms_prefix traces b initial fixed start installed c prev ((Path.here.ordinary ticket).append suffix)
      ((Path.append_cut_assoc prev (Path.here.ordinary ticket) suffix).symm.trans joined)
    exact returned_pitch traces b initial fixed installed args roles numbers age
      ⟨c,.ordinary prev ticket suffix joined⟩ prior payload (groups _)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed =>
    have prior:=rooms_prefix traces b initial fixed start installed c prev ((Path.here.reset closed).append suffix)
      ((Path.append_cut_assoc prev (Path.here.reset closed) suffix).symm.trans joined)
    exact returned_pitch traces b initial fixed installed args roles numbers age
      ⟨c,.reset prev closed suffix joined⟩ prior payload (groups _)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
