import OAI.Hierarchy.DescentDatedNativeTicketWork
import OAI.Hierarchy.DescentDatedSortedOperandCharge
import OAI.Hierarchy.DescentDatedReadPipelineFee
import OAI.Hierarchy.DescentFundedResolverCharge
import OAI.Hierarchy.DescentOrdinaryDatedEntry

namespace OAI
/-! # The native resolver prices the eight genuine final ticket expressions -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedAddressBook DescentCompiler.TerminalScale
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor : ℕ)
local notation "ext" => v.argumentUnitFrom prior floor
local notation "W" => v.registeredFrom prior floor
local notation "A" => v.registeredEntry prior floor
local notation "u₁" => 2^v.area.k*v.fundedWorkingUnit ext

def resolverCharge (h unit ratio : ℕ) :=
  let l:=v.resolver
  let F:=v.resolverFactor 745
  F*ratio*(h+l.hosts*h+l.hosts*l.groups*unit)+16384*(l.pageFactor+1)*ratio*2^(h/2)*h

theorem registered_resolver_fee (c : (W).SignedChart) (capacity : prior.argumentsPerNode≤ v.vector.operands)
    (blocks : (W).resolver.blocks=(W).material.blocks) (w ratio : ℕ)
    (paid : 0<v.venue.paidBits) (covered : v.venue.paidBits≤ v.area.unit)
    (wide : 4*v.fundedMaxUnit ext*2^v.area.k≤ v.payload) (bus : w≤ ratio*v.payload)
    (fit : (W).endAddress floor<2^w) (concat : (W).resolver.lanes*DescentPackedOperand.unit (W).resolver.size≤ w/2) :
    let mat:=v.registered_match prior floor capacity
    let shape:=v.registered_geometry prior floor
    let values:=(W).nativeTicketExpr floor c A mat shape blocks
    ((W).grainPhase floor w).wordInvoice+((W).rasterPhase floor values w).wordInvoice+
      ((W).resolvePhase floor w shape fit concat).wordInvoice≤(W).resolverCharge v.payload u₁ ratio :=by
  intro mat shape values
  have caps:=v.funded_argument_bounds ext (v.datedEntry prior floor) paid covered wide
  have widths:=v.registered_width prior floor
  have m : (W).resolver.lanes≤(A).clip.working:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have bounded (j : Fin 16) : (W).argumentWidths A j*(W).resolver.lanes≤ v.payload/2:=
    ((Nat.mul_le_mul_left _ m).trans (widths.1 j)).trans (by omega)
  have heads:=(W).native_ticket_work floor c A mat shape blocks
  let g:=(W).ticketReadGeometry
  let codes:=(W).nativeTicketSources floor c A mat shape blocks
  let start:=(W).operandRootBase floor
  have ready:=SortedInput.sources_work g codes (SortedInput.Broadcast.finish g start) 32 heads (by decide)
  have work:=expression_charge g (SortedInput.sources g codes (SortedInput.Broadcast.finish g start))
    (SortedInput.readBase g start) 32 ready (by decide)
  exact (W).resolver_charge floor w v.payload ratio u₁ 745 values shape fit concat work bus caps.fill₂
    (bounded 8) (bounded 9) (bounded 10)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
