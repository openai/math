import OAI.Hierarchy.DescentRegisteredSelectorScale
import OAI.Hierarchy.DescentFundedOperandDepotCharge
import OAI.Hierarchy.DescentFundedOperandPathCharge
import OAI.Hierarchy.DescentOperandHeaderBill
import OAI.Hierarchy.DescentDatedOperandHeadBill

namespace OAI
/-! # Composition of the original operand access program on the selected registered date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedAddressBook DescentDatedSourcePathDirectory
open DescentCompiler.TerminalScale
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor w ratio : ℕ)
local notation "W" => v.registeredFrom prior floor
local notation "A" => v.registeredEntry prior floor
local notation "ext" => v.argumentUnitFrom prior floor
local notation "short" => 2^v.area.k*v.fundedWorkingUnit ext
local notation "e" => (W).material
local notation "D" => ((W).ticket.depotShape (W).short).degree

def originalReadCharge (J rate : ℕ) :=
  let h:=v.payload
  let g:=(W).ticketReadGeometry
  let core:=(W).operandDepotCharge ratio+pathCharge (e).oldHosts (e).groups D h (4*(W).signedLayout.unit) ratio+
    rankCost (e).oldHosts D h ratio
  let tables:=ratio*(327*h+115*(2*(W).resolver.nodes+4)*2^(h/2)*h)
  let factor:=scale J (22*rate)*ratio
  let rows:=h+g.hosts*h+g.hosts*g.groups*short
  core+tables+(7*(factor*rows+factor*(2^(h/2)*h))+finalCharge h ratio)

/-- The only predecessor term on the right is the separately charged two-width
transfer at its original signed input pitch. -/
theorem original_source_charge (c : (W).SignedChart)
    (capacity : prior.argumentsPerNode≤ v.vector.operands)
    (blocks : (W).resolver.blocks=(e).blocks) (J rate : ℕ)
    (selected : (W).signed=(W).signedLayout.format v.payload) (cap : 256≤(W).prior.placement.cap)
    (oldRoom : 2*(W).fundedPanelUnit≤ v.payload) (newRoom : 2*(W).signedLayout.unit≤ v.payload)
    (paid : 0<v.venue.paidBits) (covered : v.venue.paidBits≤ v.area.unit)
    (wide : 4*v.fundedMaxUnit ext*2^v.area.k≤ v.payload) (bus : w≤ ratio*v.payload)
    (cost : ∀j,(W).ticketReadGeometry.coefficientInputs 32 short j≤ scale J rate) :
    let mat:=v.registered_match prior floor capacity
    let shape:=v.registered_geometry prior floor
    ((W).originalSourcePhase floor w c A mat shape blocks).wordInvoice≤
       v.originalReadCharge prior floor ratio J rate+((W).headTransferPhase floor c w).wordInvoice :=by
  intro mat shape
  have old:=(W).operand_depot_charge A floor w ratio selected cap oldRoom newRoom bus
  have hops:=(W).operand_path_charge floor w ratio selected newRoom bus
  change _ ≤ pathCharge (e).oldHosts (e).groups D v.payload (4*(W).signedLayout.unit) ratio +
    rankCost (e).oldHosts D v.payload ratio at hops
  have header:=v.registered_header_cost prior floor w ratio bus
  have picked:=(v.registered_selector_charge prior floor c capacity blocks ((W).operandRootBase floor)
    w ratio J rate paid covered wide bus cost).1
  unfold originalSourcePhase sortedTicketPhase operandEarlyPhase
  simp only [NativePhase.wordInvoice_seq]
  dsimp only [originalReadCharge]
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
