import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentScheduledPaddedRun
import OAI.Hierarchy.DescentResetSlotIndex
import OAI.Hierarchy.DescentDatePortArchiveFits
import OAI.Hierarchy.DescentRegisteredVenueDegree

namespace OAI
/-! # Admitting a reset at the actual sparse instruction of a registered chronology -/
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

theorem Menu.receiverWidth_at {F : Type} [Field F] {n degree : ℕ}
    (b : Menu n degree) (G : PoweredGadget F) (S : AtomSchedule) (k i : ℕ) (port : DatePorts) (baseAddress : ℕ) :
    (PhysicalReset.scheduled G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload b.ordinary b.op
      (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) port.operandLanes port.roleLanes port.venue
      port.io.wire port.io.roster baseAddress).successor.groupWidth = b.receiverWidth G S k i port := by
  have inventory := PhysicalReset.selected_inventory G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit b.payload
    (NativePitch.resetCut S k b.tail b.p b.f b.payload i)
    (NativePitch.incoming S k b.tail b.p b.f b.payload b.ordinary (i+1)) b.op.C b.op.w
    port.operandLanes port.roleLanes
    (DescentPrimitivePalette.printedBits G (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) b.op)
    port.venue port.io.wire port.io.roster baseAddress
  exact congrArg₂ (fun rs ts : List ℕ => 1+(rs++ts).sum) inventory.1 inventory.2.1

private theorem epoch_length (t J : ℕ) : (kindCalendar t J).length=(t+1)*J:=by
  induction J with
  | zero=>rfl
  | succ J ih=>
    rw [kindCalendar,List.replicate_succ,List.flatten_cons,List.length_append]
    change (kindPeriod t).length+(kindCalendar t J).length=_
    rw [ih,Nat.mul_succ]
    simp [kindPeriod,Nat.add_comm]

omit [Fintype P] in
/-- All successful and malformed tapes see one chosen instruction after the very
same geometrically admitted predecessor, including its paid shrinking-archive scan. -/
theorem reset_issued_any (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ) (e : RunTrace.Events traces i)
    (reset : e.2.isReset=true) (geom : Geometry G S b k w i (current i))
    (short : 8*b.receiverWidth G S k i (current i).ports≤b.payload) (bus : b.payload≤w)
    (degreeRoom : (current i).ports.venue.degree+1<2^w) (top : (outer i).fullEnd<2^w) :
    ∃move : Move w,issued traces b i e (current i) move ∧ move.next.floor=(outer i).fullEnd ∧
      ∀m,∃dst,move.code.Runs m dst ∧ move.code.cheap ∧
        ∀z,z<(current i).floor ∨ move.next.floor≤z→dst z=m z :=by
  have stamp := e.2.shown
  rw [tags e.1,reset] at stamp
  have slot:=reset_slot_index S.rounds S.height i stamp
  have within : i<S.length:=by
    rw [List.head?_drop] at stamp
    have lt: i<(epochs).length:=(List.getElem?_eq_some_iff.mp stamp).choose
    simpa only [epoch_length,AtomSchedule.length] using lt
  have pitch := geom.format.pitch within
  simp only [NativePitch.incoming, ite_eq_left within, ite_eq_left slot] at pitch
  have groups : S.baseGroups=2^b.tail:=by
    obtain ⟨t,r,J,M,eqn⟩:=geom.room.scheduled
    exact congrArg AtomSchedule.baseGroups eqn
  let site:=(current i).ports
  have args : (outer i).inner.successor.setup.retained.previousArgs=site.argumentsPerNode:=geom.arguments.symm
  have phaseShort : 8*(outer i).inner.successor.groupWidth ≤ b.payload :=
    (Nat.mul_le_mul_left 8 (b.receiverWidth_at G S k i site (site.priorStart k (current i).floor)).le).trans short
  obtain ⟨room,run⟩:=scheduled_padded_any G S b.board k b.tail i b.p b.f b.gain b.drift b.degreeLimit
    b.payload b.ordinary b.op (S.firstWidth G.b b.p) (S.grainAt G.b b.p 0) site (current i).floor w
    geom.room.hosts geom.format.width geom.capacity geom.room.population.groups pitch groups geom.room.radix
    within geom.room.header geom.room.wires geom.room.paid phaseShort bus degreeRoom top
    (geom.archive.data (outer i).inner.successor.setup.retained) geom.archive.blocks geom.archive.roles args
  let move:=resetMove (G:=G) (S:=S) b k i w (current i) geom.capacity room
  refine ⟨move,?_,rfl,run⟩
  rcases e with ⟨c,event⟩
  cases event with
  | ordinary before t after atDate=>cases reset
  | reset before t after atDate=>exact ⟨geom.capacity,room,rfl⟩

omit [Fintype P] in
theorem reset_fitsAt (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ) (e : RunTrace.Events traces i)
    (reset : e.2.isReset=true) (short : 8*b.receiverWidth G S k i (current i).ports≤b.payload)
    (bus : b.payload≤w) (degreeRoom : Geometry G S b k w i (current i)→(current i).ports.venue.degree+1<2^w)
    (top : (outer i).fullEnd<2^w) : fitsAt traces b initial (w:=w) i e :=by
  intro geom
  obtain ⟨move,issued_,end_,_⟩:=reset_issued_any traces b initial tags i e reset geom short bus (degreeRoom geom) top
  exact ⟨move,issued_,end_.trans_lt top,fun _=>short⟩

omit [Fintype P] in
/-- The public bound on the largest degree buys space for the degree sentinel
at every reset, including one occurring before the first ordinary step. -/
theorem reset_fits (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ) (e : RunTrace.Events traces i)
    (reset : e.2.isReset=true) (short : 8*b.receiverWidth G S k i (current i).ports≤b.payload)
    (bus : b.payload≤w) (seedDegree : initial.ports.venue.degree=3) (degreeLimit : maximumDegree (S.rounds+1)+1<2^w)
    (top : (outer i).fullEnd<2^w) : fitsAt traces b initial (w:=w) i e :=
  reset_fitsAt traces b initial tags i e reset short bus
    (fun _=>calendar_degree_room traces b tags initial seedDegree degreeLimit i) top

omit [Fintype P] in
/-- The two global scheduling estimates may use dimensions of the actual
incoming register block at this cut. -/
theorem reset_fits_from_geometry (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ)
    (e : RunTrace.Events traces i) (reset : e.2.isReset=true)
    (bus : b.payload≤w) (seedDegree : initial.ports.venue.degree=3) (degreeLimit : maximumDegree (S.rounds+1)+1<2^w)
    (short : Geometry G S b k w i (current i)→8*b.receiverWidth G S k i (current i).ports≤b.payload)
    (endRoom : Geometry G S b k w i (current i)→(outer i).fullEnd<2^w) :
    fitsAt traces b initial (w:=w) i e :=
  fun geom=>reset_fits traces b initial tags i e reset (short geom) bus seedDegree degreeLimit (endRoom geom) geom

omit [Fintype P] in
/-- The selected program at the original cut is exactly the padded reset on
every tape, with no successful parse or well-formed archive required to run. -/
theorem reset_instruction (tags : ∀c,(traces c).path.kinds=epochs) (i : ℕ) (e : RunTrace.Events traces i)
    (reset : e.2.isReset=true) (geom : Geometry G S b k w i (current i))
    (short : 8*b.receiverWidth G S k i (current i).ports≤b.payload)
    (bus : b.payload≤w) (seedDegree : initial.ports.venue.degree=3) (degreeLimit : maximumDegree (S.rounds+1)+1<2^w)
    (top : (outer i).fullEnd<2^w) :
    (current (i+1)).floor=(outer i).fullEnd ∧
    ∀m : Memory w,∃dst,(instruction (w:=w) traces b initial i).Runs m dst ∧ (instruction (w:=w) traces b initial i).cheap ∧
      ∀z,z<(current i).floor ∨ (current (i+1)).floor≤z→dst z=m z :=by
  obtain ⟨move,hit,end_,runs⟩:=reset_issued_any traces b initial tags i e reset geom short bus
    (calendar_degree_room traces b tags initial seedDegree degreeLimit i) top
  have fixed (other : RunTrace.Events traces i) (step : Move w) (atCut : issued traces b i other (current i) step) : step=move :=
    reset_unique traces b i other e (current i) step move
      ((other.2.compatible e.2 ((tags other.1).trans (tags e.1).symm)).trans reset) reset atCut hit
  have result:=returned traces b initial i e move hit fixed
  rw [result.1,result.2]
  exact ⟨end_,runs⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
