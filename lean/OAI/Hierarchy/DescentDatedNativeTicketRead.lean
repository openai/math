import OAI.Hierarchy.DescentDatedOperandTicketValue
import OAI.Hierarchy.DescentDatedTicketDigit

namespace OAI
/-! # A physical output lane of the native 17-input ticket pipeline -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM

open scoped Fin.CommRing

variable (g : Geometry) (v : Data g) (s : Sources g) {w floor : ℕ} (m : Memory w)

def readTicket (job : Fin g.jobs) (actor : Fin g.hosts) (group : Fin g.groups) (f : Fin 8) :=
  Ticket.socketDigit g.resultBits g.lanes (expression g s floor job f) ((phase g s floor w).image m) actor group

theorem ticket_read (stored : Recorded g s v floor m) (space : endAddress g floor < 2^w)
    (lanes : 0 < g.lanes) (width : g.resultBits*g.lanes ≤ w)
    (job : Fin g.jobs) (actor : Fin g.hosts) (group : Fin g.groups) (f : Fin 8) :
    readTicket g s (floor:=floor) m job actor group f=((ticketAt g v job actor group f:ℕ):Cell g.resultBits).val :=by
  have trace:=(observed_ticket g v s m stored space).2 job f
  exact Ticket.socket_digit _ _ _ trace.read lanes width actor group

theorem ticket_read_of_lt (stored : Recorded g s v floor m) (space : endAddress g floor < 2^w)
    (lanes : 0 < g.lanes) (width : g.resultBits*g.lanes ≤ w)
    (job : Fin g.jobs) (actor : Fin g.hosts) (group : Fin g.groups) (f : Fin 8)
    (fits : ticketAt g v job actor group f < 2^g.resultBits) :
    readTicket g s (floor:=floor) m job actor group f=ticketAt g v job actor group f :=by
  rw [ticket_read g v s m stored space lanes width job actor group f,Fin.val_cast_of_lt fits]

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
