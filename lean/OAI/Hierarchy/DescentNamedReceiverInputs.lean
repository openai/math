import OAI.Hierarchy.DescentResetReceiverScale

namespace OAI
/-! # Reducing the full reset aperture to the original schedule, root census, and operand alphabet -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSixParty DescentCompiler DescentSIMDLookup DescentResetLocalRoster Filter
open DescentCompiler.TerminalScale DescentFallbackPeriod
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2600000

structure Sample where
  sched : AtomSchedule
  k : ℕ
  tail : ℕ
  age : ℕ
  p : ℕ
  drift : ℕ
  degree : ℕ
  payload : ℕ
  root : ℕ
  previous : ℕ
  lanes : ℕ
  nextLanes : ℕ
  base : ℕ
  prior : Prior

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (board : NonlinearExpanders.Graph n d)
variable (D f g C packet : ℕ)

def Sample.output (z : Sample) : ResetOutput :=
  let old : Prior := {z.prior with venue:={z.prior.venue with degree:=D}}
  fromBoard G z.sched board z.k z.tail z.age z.p f g z.drift z.degree z.payload z.root z.previous
    z.lanes z.nextLanes C packet old z.base

variable {ι : ℕ→Type*} (J : ℕ→ℕ) (z : ∀h,ι h→Sample)
local notation "v" => fun h i=>(z h i).output G board D f g C packet
local notation "Ht" => GroupStage.depthBound D n f g

/-- The root palette, node schema and newly printed role each have one independent
original bound. The map of earlier absolute addresses does not enter these estimates. -/
structure CalendarInputs : Prop where
  sheets : CandidateSheets.LocalFields J (fun h i=>(v h i).sheets) (fun h i=>(v h i).front.peer.shapes)
    (fun h i=>(v h i).ticketBits)
  previousCap : SmallAt J fun h i=>let a:=z h i;((capCalendar G.b a.sched.rounds g a.sched.height).take a.age).prod*256
  dimension : SmallAt J fun h i=>let a:=z h i;a.sched.groupWidth a.k a.tail a.age+a.k
  controls : SmallAt J fun h i=>let a:=v h i;a.middle.rootControlBits a.front.donor.cap
  rootOutput : SmallAt J fun h i=>(v h i).rootOutputBits
  funded : SmallAt J fun h i=>(v h i).venue.census.broadcast
  paid : SmallAt J fun h i=>(z h i).prior.venue.paidBits
  coefficient : SmallAt J fun h i=>let a:=z h i;DescentOperandWidth.recordBits G a.sched a.k a.tail a.drift a.degree a.p
  primitive : SmallAt J fun h i=>(z h i).prior.printedBits
  «arguments» : SmallAt J fun h i=>let a:=z h i;a.sched.retainedArgumentsAt G a.drift
  nodes : SmallAt J fun h i=>(z h i).sched.retainedNodes
  fibres : ∀h i,(v h i).setup.retained.donors=2^(z h i).k

attribute [local irreducible] SmallAt

theorem from_calendar_inputs (r : CalendarInputs G board D f g C packet J z) :
    LocalInputs J v :=by
  let cap (a:Sample):=((capCalendar G.b a.sched.rounds g a.sched.height).take a.age).prod*256
  let field (a:Sample):=ResetMiddle.fieldWidth D (cap a) n a.k Ht
  let secret (a:Sample):=ResetMiddle.privateWidth board a.k Ht f (cap a) C packet
  have L : SmallAt J fun h i=>2^(z h i).k:=r.sheets.block
  have kk : SmallAt J fun h i=>(z h i).k:=L.of_le fun _ _=>Nat.lt_two_pow_self.le
  have root : SmallAt J fun h i=>field (z h i):=by
    apply r.controls.of_le
    intro h i
    let a:=v h i
    let m:=a.middle
    let N:=DescentFallbackPeriod.Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) a.front.donor.cap m.rotorBits m.rootDepth
    have member:=m.rootControl_le a.front.donor.cap (m.rootField*(N+1)) (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos N)).trans member
  have privateField : SmallAt J fun h i=>secret (z h i):=by
    apply r.rootOutput.of_le
    intro h i
    have high:0<DescentResetCableSlots.cableCap board Ht :=lt_of_lt_of_le (Nat.two_pow_pos _) (Nat.le_max_right ..)
    let width:=secret (z h i)
    have bound : width≤width*(DescentResetCableSlots.cableCap board Ht*5):=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos high (by decide))
    exact bound.trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have signed : SmallAt J fun h i=>DescentSignedCableCodec.width D (cap (z h i)) :=
    r.sheets.old.of_le fun _ _=>Nat.le_max_left ..
  have roster : SmallAt J fun h i=>(v h i).front.peer.shapes:=r.sheets.shapes
  have q : SmallAt J fun h i=>Nat.clog 2 (2*((v h i).sheets.candidates)+1):=
    (((SmallAt.const J 2).mul r.sheets.slots).add (SmallAt.const J 1)).clog
  have keyBits : SmallAt J fun h i=>(v h i).setup.fieldBits :=
    r.coefficient.max ((SmallAt.const J 1).max (signed.max r.sheets.meta))
  have resultBits : SmallAt J fun h i=>(v h i).setup.rotorBits :=
    keyBits.max (q.max (root.max privateField))
  have inc : SmallAt J fun h i=>cap (z h i):=r.previousCap
  have gate : SmallAt J fun h i=>(v h i).sheets.metaBits:=r.sheets.meta
  have stem : SmallAt J fun h i=>(v h i).sheets.stemBits:=r.sheets.old
  have count : SmallAt J fun h i=>DescentRotorWindowArchive.count D (2^(z h i).k) (cap (z h i)):=by
    exact (((L.add ((SmallAt.const J D).mul L)).add (L.mul ((SmallAt.const J 2).mul inc))).add
      ((L.mul L).add (SmallAt.const J (D*(D*6)))))
  have shapeRows : SmallAt J fun h i=>DescentFallbackShapeTable.rows (z h i).k (2^n):=
    ((kk.add (SmallAt.const J 1)).mul L).mul (SmallAt.const J _)
  have constantBook : SmallAt J fun h i=>DescentSharedBookScan.width (z h i).k (2^n) D:=
    shapeRows.mul ((SmallAt.const J _).mul shapeRows)
  have receipt : SmallAt J fun h i=>DescentFallbackPeriod.inputCount D (2^(z h i).k) (cap (z h i)) n (z h i).k:=by
    exact (L.add ((SmallAt.const J D).mul L)).add ((L.mul ((SmallAt.const J 2).mul inc)).add constantBook)
  exact {
    sheets:=r.sheets,
    argumentCap:=r.arguments,rootBlocks:=L,rootHeaders:=r.controls,
    rootOutput:=r.rootOutput,
    cost:=r.funded,
    precision:=r.paid,
    projection:=root,
    rootDegree:=SmallAt.const J D,
    degree:=SmallAt.const J D,
    stemField:=root,
    privateWidth:=privateField,
    wires:=SmallAt.const J (DescentResetCableSlots.cableCap board Ht),
    donor:=root,
    returned:=by
      change SmallAt J (fun h i=>1+((D*(2*cap (z h i)))*2+D*D))
      exact (SmallAt.const J 1).add ((((SmallAt.const J D).mul ((SmallAt.const J 2).mul inc)).mul (SmallAt.const J 2)).add (SmallAt.const J (D*D))),
    query:=SmallAt.const J (Nat.clog 2 (D+2)),
    cargo:=SmallAt.const J (Nat.clog 2 (D+3)),
    contact:=root,
    oldFields:=count,
    root:=root,
    fallback:=receipt,
    matrix:=count,
    token:=r.primitive,
    tokenNodes:=r.nodes,
    opcodes:=SmallAt.const J _,
    casts:=root.max (stem.max gate),
    birthClass:=((SmallAt.const J 6).add ((SmallAt.const J 2).mul (L.mul (SmallAt.const J (2^n))))).clog,
    birthBits:=SmallAt.const J _,birthPaid:=r.paid,birthSpan:=r.coefficient,
    oldToken:=r.primitive,
    signedQuery:=q,
    signedRaw:=r.sheets.meta,
    signedValue:=r.coefficient,
    nodeWidth:=r.coefficient,
    nodes:=r.nodes,
    nextSigned:=by
      let u:=(((SmallAt.const J (2^g)).mul r.previousCap).add (SmallAt.const J 1)).clog
      exact ((SmallAt.const J (3+1)).clog).add (u.add (u.add (u.add (SmallAt.const J 2)))),
    paid:=r.paid,
    span:=r.coefficient,
    arity:=r.coefficient,
    retained:=r.coefficient,
    signed:=root,
    oldOrder:=r.sheets.meta,
    newInput:=keyBits,
    donors:=L.of_le fun h i=>(r.fibres h i).le,
    cap:=r.previousCap,
    rotor:=resultBits,
    packet:=resultBits,
    peer:=(((SmallAt.const J (D+1)).mul roster).add (SmallAt.const J 1)).clog,
    marker:=(((SmallAt.const J (D+1)).mul roster).add (SmallAt.const J 1)).clog,
    donorBoard:=count.add constantBook,
    donorLanes:=(SmallAt.const J 2).mul ((L.mul ((SmallAt.const J 2).mul inc)).mul (SmallAt.const J 3)),
    view:=root.mul ((SmallAt.const J 2).mul ((L.mul ((SmallAt.const J 2).mul inc)).mul (SmallAt.const J 2))),
    actor:=(((SmallAt.const J 2).mul kk).add (SmallAt.const J n) |>.add (SmallAt.const J 2) |>.mul L).add (((r.dimension.max (SmallAt.const J (Nat.clog 2 (D*2^Ht)))).add (SmallAt.const J 2)).clog),
    packetSize:=(((SmallAt.const J 8).add ((SmallAt.const J 12).mul (L.mul ((SmallAt.const J 2).mul inc)))).add receipt).add ((L.mul L).add (SmallAt.const J (D*(D*6)))) }

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
