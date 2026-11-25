import OAI.Hierarchy.DescentNamedRecordedVenue
import OAI.Hierarchy.DescentNamedPriorVenueRoom
import OAI.Hierarchy.DescentRecordedOperandLocations

namespace OAI
/-! # The selected native census has the original reached actor dimensions -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentDatedAddressBook DescentDenseHostOrder DescentSIMDLookup DescentSixParty.Chronology
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist:ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {prev:Reached W G q ε S k i z D wire hist} (B:ClosedReset prev ctl)
  (p drift degree payload e previous M nextM packet:ℕ) (prior:ResetOutput.Prior) (base : ℕ)
local notation "v" => ResetOutput.fromBoard G S ctl.board k tail i p f g drift degree payload e previous M nextM C packet prior base
local notation "L" => (capCalendar G.b S.rounds g S.height).take i
local notation "H" => S.hostSize i
local notation "cc" => B.terminals.commonDepth
local notation "Q" => (DescentDenseHostOrder.roster B.reset.graph (B.reset.k-cc) (GroupStage.depthBound D n f g)).card
local notation "ac" => (v).actor
local notation "jobs" => (v).venue.census

theorem named_operand_geometry (ports:prior.venue.degree=D) (blocks:prior.venue.k=k)
    (oldHosts:prior.venue.hosts=H) (cap:prev.placement.cap=(L).prod*256) (pos:0<M) :
    (jobs).jobs=(ac).shapes ∧ (jobs).hosts=(ac).hosts ∧ (jobs).groups=(ac).groups ∧
    (ac).hosts=H ∧ (ac).shapes=Q ∧ (ac).chunksPerHost=chunks (2^cc) (2^e) ∧
    (v).front.peer.hosts=H*Q ∧ (v).receiver.blocks=2^k ∧ (v).receiver.capacity=B.next.placement.cap:=by
  obtain ⟨_,jobsAt,sitesAt,waves,_,_,_⟩:=ResetOutput.venue_faces G S ctl.board k tail i p f g drift degree
    payload e previous M nextM C packet prior base oldHosts blocks ctl.base ctl.radix B.age pos
  have sizes : (ac).shapes=Q:=by
    change (DescentDenseHostOrder.roster ctl.board k (GroupStage.depthBound prior.venue.degree n f g)).card=Q
    rw [ports]
    exact (DescentExteriorReplay.HopTables.reset_public B).1.symm
  refine ⟨jobsAt,sitesAt,waves,rfl,sizes,?_,?_,rfl,?_⟩
  · change chunks (2^S.groupWidth k tail i) (2^e)=chunks (2^cc) (2^e)
    rw [B.commonDepth]
  · change H*(ac).shapes=H*Q
    rw [sizes]
  · change 2^g*((L).prod*256)=B.next.placement.cap
    rw [←cap,B.next_capacity]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
