import OAI.Hierarchy.DescentNamedOperandActorGeometry
import OAI.Hierarchy.DescentNamedResetDateInputs

namespace OAI
/-! Numerical rooms for a captured actor event on the original named reset. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentDenseHostOrder
open DescentColonies ProtocolRAM DescentSixParty.Chronology DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F X : Type} [Field F] {d : ℕ} {bits : X→ℕ} {W : MarkedWorld F d X bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z wire hist D n h₀ C f g cut tail : ℕ}
  {old : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h₀ C f g cut tail}
  (B : ClosedReset old ctl)
variable (p drift degree h e prev M nextM operandLanes roleLanes printed : ℕ)
  (previous : StageVenueTail.Date) (io : Dated.Operands) (outer w : ℕ)
local notation "packet" => ctl.bitsR
local notation "a" => named G S ctl.board k tail age p f g drift degree h e prev M nextM C packet
  operandLanes roleLanes printed previous io.wire io.roster outer
local notation "u₀" => (a).stageStart outer
variable (u : (named G S ctl.board k tail age p f g drift degree h e prev M nextM C ctl.bitsR
    operandLanes roleLanes printed previous io.wire io.roster outer).DateInputs
    ((named G S ctl.board k tail age p f g drift degree h e prev M nextM C ctl.bitsR
      operandLanes roleLanes printed previous io.wire io.roster outer).stageStart outer) w)
local notation "b" => (a).rebased u₀
local notation "v" => (a).successor
local notation "src" => FinalInputs.predecessor u
local notation "prior" => ResetOutput.Prior.atDate G S age p drift operandLanes roleLanes printed previous
local notation "H" => S.hostSize age
local notation "N" => Fintype.card B.next.V
local notation "cc" => B.terminals.commonDepth
local notation "Q" => (roster B.reset.graph (B.reset.k-cc) (GroupStage.depthBound D n f g)).card
local notation "R" => H*Q
local notation "stop₀" => (v).finalEnd b
local notation "fund" => (v).fundedEnd b
local notation "V" => ClosedReset.Window.calibrated B (v).venue.census H (S.hostSize (age+1)) (2^e) (2^e) M nextM previous.paidBits
local notation "out" => (V).sources (src) fund

set_option maxHeartbeats 750000 in
theorem DateInputs.fromNamed_held_bounds (ready : u.Ready) (ports : previous.degree=D)
    (blocks : previous.k=k) (sizes : previous.hosts=H)
    (cap : old.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256) (pos : 0<M) :
    (v).venue=V ∧ (v).front.peer.hosts=R ∧ N≤(src).ranks.inverse.size ∧ N<2^w ∧
    (src).actor.base+Q*(H*chunks (2^cc) (2^e))≤ stop₀ ∧ (src).ranks.count.base<stop₀ ∧
    (src).ranks.inverse.base+N≤ stop₀ ∧ (src).ranks.forward.base+R≤ stop₀ ∧
    (∀j,((src).ranks.neighbor j).base+R≤ stop₀) ∧ R≤(src).ranks.forward.size ∧
    (∀j,R≤((src).ranks.neighbor j).size) ∧
    (∀x:Block k,((out).paid x.val).base+((out).paid x.val).size≤(V).actorStart fund) ∧
    (∀x:Block k,((out).alive x.val).base+((out).alive x.val).size≤(V).peerStart fund) ∧
    ∀(x:Block k)(j:Fin (2*B.next.placement.cap)),((src).signed x.val j.val).base+((src).signed x.val j.val).size≤ stop₀:=by
  have geo : (v).venue.census.jobs=(v).actor.shapes ∧ (v).venue.census.hosts=(v).actor.hosts ∧
      (v).venue.census.groups=(v).actor.groups ∧ (v).actor.hosts=H ∧ (v).actor.shapes=Q ∧
      (v).actor.chunksPerHost=chunks (2^cc) (2^e) ∧ (v).front.peer.hosts=R ∧
      (v).receiver.blocks=2^k ∧ (v).receiver.capacity=B.next.placement.cap := by
    rw [named_successor]
    exact ClosedReset.Window.named_operand_geometry B p drift degree h e prev M nextM packet prior b
      ports blocks sizes cap pos
  obtain ⟨jobs,sites,waves,hosts,shape,chunk,peer,bks,lim⟩:=geo
  have venue : (v).venue=V := by
    rw [named_successor]
    exact ClosedReset.Window.named_venue B p drift degree h e prev M nextM packet prior b ports blocks sizes cap
  obtain ⟨inv,rng,actors,count,invCut,fwCut,prCut,fw,prs,sig⟩:=
    ClosedReset.Window.operand_locations B («H»:=H) (Ma:=2^e) (w:=w) old.valid.host («a»:=a) (floor:=u₀) (u:=u) ready jobs sites waves hosts shape chunk peer bks lim ready.full
  have issued (x:Block k):=(V).earlier_sheets (src) fund (show (V).dense.blocks=2^k from rfl) x
  exact ⟨venue,peer,inv,rng,actors,count,invCut,fwCut,prCut,fw,prs,fun x=>(issued x).1,fun x=>(issued x).2,sig⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
