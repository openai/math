import OAI.Hierarchy.DescentDatedTicketKeyRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryStep

namespace OAI
/-! # Routed ticket codes at the physical ordinary date -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

/-- Clipping the two working pitches and reserving the routed socket area preserve
the chosen short-record width and the authenticated predecessor catalogue. -/
theorem registered_ticket_ordinal_room (growth : 0 < S.capGain) (date : i < S.length) :
    22*((v).ticket.depotShape (v).short).cap+10 < 2^((v).resolver.size+2) :=by
  have width := (OrdinaryBooks.record_width G S op gain k i p tail drift degree payload seats prior).1
  change 22*prevWorld.placement.cap+10 < 2^((books).resolver.size+2)
  rw [width]
  exact DescentOperandWidth.ticket_ordinal_room G S growth date prevWorld.valid.capacity

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
