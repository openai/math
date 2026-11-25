import OAI.Hierarchy.DescentDatedTicketWords
import OAI.Hierarchy.DescentRegisteredOperandSource

namespace OAI
/-! The four scalar side flags and three selector fields read from each physical eight-word ticket. -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentDatedOperandCoordinates DescentPriorOperandColumns DescentOperandStateBanks
noncomputable section

abbrev measuredSides (l : Layout)
    (digits : Fin l.jobs → Fin l.hosts → Fin l.groups → Fin 8 → ℕ) (grain : Cell (l.size+2)) :
    Fin l.jobs → Fin l.hosts → Fin l.groups → Side l.size :=
  fun j h g=>DescentDatedPublicGrain.withGrain grain (Ticket.recordedSide l.size (digits j h g))

abbrev measuredRoles (l : Layout)
    (digits : Fin l.jobs → Fin l.hosts → Fin l.groups → Fin 8 → ℕ) :
    Fin l.jobs → Fin 3 → Fin l.hosts → Fin l.groups → Cell (l.size+2) :=
  fun j f h g=>Ticket.recordedRole l.size (digits j h g) f

end
end Hierarchy.DescentDatedPriorOperand

end OAI
