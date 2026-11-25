import OAI.Hierarchy.DescentIssuedOrdinaryInvoice
import OAI.Hierarchy.DescentRegisteredResolverFee
import OAI.Hierarchy.DescentFundedIngressBill
import OAI.Hierarchy.DescentFundedGatherCharge
import OAI.Hierarchy.DescentPhysicalInputFee
import OAI.Hierarchy.DescentOriginalSourcePaid

namespace OAI
/-! # The operative twelve-phase operand price on the fully registered chronological date -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentDatedOperandReadPipeline
noncomputable section

private theorem charge_program {w} (p : Procedure w) (ticks : ℕ) :
    codeCharge w (7*w) ticks p=DateBill.bitTariff p ticks:=by
  unfold codeCharge DateBill.bitTariff;ring
private theorem charge_phase {w} (p : NativePhase w) :
    phaseCharge w (7*w) p=p.wordInvoice:=charge_program p.program p.ticks

variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor w ratio : ℕ)
local notation "W" => v.registeredFrom prior floor
local notation "A" => v.registeredEntry prior floor
local notation "ext" => v.argumentUnitFrom prior floor
local notation "u₀" => v.fundedWorkingUnit ext
local notation "u₁" => 2^v.area.k*u₀

/-- Contains only numerical charges for the clipped venue, registered dictionaries,
reference gather, and eight genuine source expressions resolved into seven final fields. -/
def registeredEntryCharge :=
  v.ingressCharge ext v.payload ratio+(W).dictionaryCharge A v.payload u₀ ratio+
    (W).gatherCharge v.payload u₀ u₁ ratio+(W).resolverCharge v.payload u₁ ratio

set_option maxHeartbeats 600000 in
theorem registered_entry_charge (c : (W).SignedChart) (capacity : prior.argumentsPerNode≤ v.vector.operands)
    (blocks : (W).resolver.blocks=(W).material.blocks) (pg : Fin (7*(W).vector.operands))
    (paid : 0<v.venue.paidBits) (covered : v.venue.paidBits≤ v.area.unit)
    («matching» : 2^v.area.k+1≤ v.area.unit)
    (wide : 4*v.fundedMaxUnit ext*2^v.area.k≤ v.payload) (bus : w≤ ratio*v.payload)
    (chunk : ((A).population W floor).chunkBits≤ v.payload/4)
    (menus : ((A).population W floor).count≤2^(v.payload/4)) (addr : ((W).refChart floor).endAddress<2^w)
    (fit : (W).endAddress floor<2^w) (packed : (W).resolver.lanes*DescentPackedOperand.unit (W).resolver.size≤ w/2) :
    let mat:=v.registered_match prior floor capacity
    let shape:=v.registered_geometry prior floor
    let values:=(W).nativeTicketExpr floor c A mat shape blocks
    let maker:=(W).nativeTicketPreparation floor w c A mat shape blocks pg
    (W).entryFee floor A mat values maker shape fit packed ≤
      v.registeredEntryCharge prior floor ratio+(W).inputFee A floor w+maker.wordInvoice :=by
  intro mat shape values maker
  let E:=v.datedEntry prior floor
  let other:=purchase (v.withFundedArguments 0 E).ticketReadGeometry
  have ingress:=v.funded_ingress_bill ext (A).venue ((W).signedEnd floor) w ratio «matching» paid covered wide bus
  have earlyMatch := v.funded_match ext E floor rfl capacity
  have charts:=v.funded_dictionary_charge E other floor w ratio paid covered wide bus earlyMatch chunk menus addr
  have gather:=v.funded_gather_charge E other floor w ratio paid covered wide bus earlyMatch
  have resolve:=v.registered_resolver_fee prior floor c capacity blocks w ratio paid covered wide bus fit packed
  change ((A).clip.phase (A).venue ((W).signedEnd floor) w).wordInvoice ≤ v.ingressCharge ext v.payload ratio at ingress
  change (((A).chip W).phase ((A).chipStart W floor) ((A).chipSource W floor) w).wordInvoice +
    (((A).population W floor).phase ((A).ports W floor) ((A).labels W floor) w).wordInvoice +
    DateBill.bitTariff (((W).refChart floor).program w) ((W).refTime floor) +
    DateBill.bitTariff ((W).bornBook.program ((A).chipBank W floor) ((W).birthStart floor) w)
      ((W).bornBook.ticks ((A).chipBank W floor) ((W).birthStart floor)) ≤
      (W).dictionaryCharge A v.payload u₀ ratio at charts
  change (((A).directory W floor mat).refs.phase w ((W).vectorStart floor)).wordInvoice ≤
    (W).gatherCharge v.payload u₀ u₁ ratio at gather
  change ((W).grainPhase floor w).wordInvoice + ((W).rasterPhase floor values w).wordInvoice +
    ((W).resolvePhase floor w shape fit packed).wordInvoice ≤ (W).resolverCharge v.payload u₁ ratio at resolve
  unfold entryFee inputFee registeredEntryCharge
  simp only [charge_phase,charge_program]
  omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
