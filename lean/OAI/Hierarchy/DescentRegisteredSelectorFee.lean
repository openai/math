import OAI.Hierarchy.DescentDatedSortedOperandCharge
import OAI.Hierarchy.DescentDatedReadPipelineFee
import OAI.Hierarchy.DescentDatedNativeTicketWork
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentFundedClipChoice
import OAI.Hierarchy.DescentSelectorWordScale

namespace OAI
/-! # Prices of the actual sorted origin and five ticket batches after the two immutable source retile passes -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedOperandReadPipeline DescentDatedAddressBook DescentCompiler.TerminalScale
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor : ℕ)
local notation "ext" => v.argumentUnitFrom prior floor
local notation "W" => v.registeredFrom prior floor
local notation "A" => v.registeredEntry prior floor
local notation "g" => (W).ticketReadGeometry
local notation "cost" => 2^v.area.k*v.fundedWorkingUnit ext

theorem registered_selector_charge (c : (W).SignedChart) (capacity : prior.argumentsPerNode≤ v.vector.operands)
    (blocks : (W).resolver.blocks=(W).material.blocks) (base w ratio J rate : ℕ)
    (paid : 0<v.venue.paidBits) (covered : v.venue.paidBits≤ v.area.unit)
    (wide : 4*v.fundedMaxUnit ext*2^v.area.k≤ v.payload) (bus : w≤ ratio*v.payload)
    (localFee : ∀i,(g).coefficientInputs 32 cost i≤ scale J rate) :
    let mat:=v.registered_match prior floor capacity
    let codes:=(W).nativeTicketSources floor c A mat (v.registered_geometry prior floor) blocks
    let units:=scale J (22*rate)
    let rows:=v.payload+(g).hosts*v.payload+(g).hosts*(g).groups*cost
    let pages:=2^(v.payload/2)*v.payload
    (SortedInput.program g codes base (W).material.oldHosts (W).materialPitch
      ((W).operandRanks floor).endpoints ((A).ports W floor).roster w).wordInvoice≤7*(units*ratio*rows+units*ratio*pages)+finalCharge v.payload ratio ∧
      ∀j f,(SortedInput.output g codes base j f).work≤745 :=by
  intro mat codes units rows pages
  have fit:=((v.registered_width prior floor).2).trans (by omega : v.payload/4≤ v.payload/2)
  have caps:=v.funded_argument_bounds ext (v.datedEntry prior floor) paid covered wide
  have authentic:= (W).native_ticket_work floor c A mat (v.registered_geometry prior floor) blocks
  have width : 0<(g).digitBits:=by
    have hb : (W).resolver.size+2≤(g).digitBits:=(W).operandWidth_le 1
    omega
  have total:=SortedInput.program_charge g codes base (W).material.oldHosts (W).materialPitch w v.payload
    ratio cost (scale J rate) ((W).operandRanks floor).endpoints ((A).ports W floor).roster
    authentic width caps.out localFee fit bus caps.fill₂
  have power : (scale J rate)^22=units:=by
    dsimp [units,scale]
    rw [←pow_mul]
    congr 1
    ring
  simpa only [power] using total

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
