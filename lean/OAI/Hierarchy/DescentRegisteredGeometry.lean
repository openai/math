import OAI.Hierarchy.DescentRegisteredPrefixRooms
import OAI.Hierarchy.DescentRegisterVenueFormat
import OAI.Hierarchy.DescentRegisteredCapacity
import OAI.Hierarchy.DescentRegisteredDegreeStep
import OAI.Hierarchy.DescentDatePortArchiveFits

namespace OAI
/-! # Physical register dimensions as inputs to the next native placement -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)

local notation "model" i:arg a:arg t:arg => DatePorts.ordinaryModel (a:Position).ports t b.op b.gain b.tail b.p b.f b.drift
  b.degreeLimit b.payload (b.seats i) (a).floor b.ordinary
local notation "resetModel" i:arg a:arg => PhysicalReset.scheduled G S b.board k b.tail i b.p b.f b.gain b.drift
  b.degreeLimit b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) (a:Position).ports.operandLanes (a).ports.roleLanes
  (a).ports.venue (a).ports.io.wire (a).ports.io.roster ((a).ports.priorStart k (a).floor)

omit [Fintype P] in
theorem output_archive (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (hit : issued traces b i e a move) (_old : VenueFormat S b k i a) :
    move.next.ports.ArchiveFits k move.next.floor :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨positive,room,rfl⟩:=hit
    let v:=model i a t
    apply DatePorts.ordinary_archive_fits v (v.stageStart a.floor) k <;> rfl
  | reset before t after eqn=>
    obtain ⟨cap,space,rfl⟩:=hit
    let v:=resetModel i a
    let floor:=(a).ports.priorStart k (a).floor
    apply DatePorts.reset_archive_fits v (v.stageStart floor) _ k <;> first | rfl

structure Geometry (G : PoweredGadget F) (S : AtomSchedule) (b : Menu n degree) (k w i : ℕ) (p : Position) : Prop where
  archive : p.ports.ArchiveFits k p.floor
  room : Rooms G S b k w i p
  format : VenueFormat S b k i p
  «arguments» : p.ports.argumentsPerNode=(if i=0 then 3*(S.firstWidth G.b b.p/b.p) else S.retainedArgumentsAt G b.drift)
  degree : p.ports.venue.degree=atRound (i%(S.rounds+1))
  capacity : p.ports.venue.cap=((capCalendar G.b S.rounds b.gain S.height).take i).prod*256

local notation "costs" => capCalendar G.b S.rounds b.gain S.height
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "data" i:arg => Geometry G S b k w i (cursor i)
variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→
    issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height) (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
variable (seed : Geometry G S b k w 0 initial)

def fitsAt (i : ℕ) (e : RunTrace.Events traces i) : Prop :=
  data i → ∃move : Move w,steps i e (cursor i) move ∧ move.next.floor<2^w ∧
    (e.2.isReset=true→8*b.receiverWidth G S k i (cursor i).ports≤b.payload)

variable (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces b initial (w:=w) i e)

include fixed caps tags placed in
omit [Fintype P] in
theorem geometry_next (i : ℕ) (e : RunTrace.Events traces i) (prior : data i) : data (i+1) :=by
  obtain ⟨move,hit,roof,short⟩:=placed i e prior
  have n:=(returned traces b initial i e move hit (fun j t hj=>fixed i j e t move hj hit)).2
  rw [n]
  exact ⟨output_archive traces b i e _ move hit prior.format,
    issued_register_room traces b i e _ move hit prior.room roof short,
    step_venue_format traces b i e _ move hit prior.format,
    by simpa only [Nat.succ_ne_zero,ite_false] using issued_arguments traces b i e _ move prior.room.args hit,
    issued_degree traces b tags i e _ move hit,issued_cap traces b caps tags i e _ move hit⟩

variable (c : C)
local notation "t" => traces c

include fixed caps tags seed placed in
omit [Fintype P] in
theorem geometry_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) : data i :=by
  induction p with
  | here=>exact seed
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick ih=>
    exact geometry_next traces b initial fixed caps tags placed age ⟨c,.ordinary prev tick suffix joined⟩
      (ih ((Path.here.ordinary tick).append suffix) ((Path.append_cut_assoc prev (Path.here.ordinary tick) suffix).symm.trans joined))
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    exact geometry_next traces b initial fixed caps tags placed age ⟨c,.reset prev closed suffix joined⟩
      (ih ((Path.here.reset closed).append suffix) ((Path.append_cut_assoc prev (Path.here.reset closed) suffix).symm.trans joined))

include fixed caps tags seed placed in
omit [Fintype P] in
theorem geometry_on_event (i : ℕ) (e : (t).path.Event i) : data i :=by
  cases e with
  | ordinary before tick after eqn=>
    exact geometry_prefix traces b initial fixed caps tags seed placed c before ((Path.here.ordinary tick).append after)
      ((Path.append_cut_assoc before (Path.here.ordinary tick) after).symm.trans eqn)
  | reset before closed after eqn=>
    exact geometry_prefix traces b initial fixed caps tags seed placed c before ((Path.here.reset closed).append after)
      ((Path.append_cut_assoc before (Path.here.reset closed) after).symm.trans eqn)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
