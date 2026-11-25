import OAI.Hierarchy.DescentOriginalSourceCharge
import OAI.Hierarchy.DescentDatedOperandHeadRows

namespace OAI
/-! # Complete native charge for the authentic ordinary raw source access -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open Filter DescentDatedAddressBook DescentDatedOperandReadPipeline DescentCompiler.TerminalScale
open DescentStaticWordColumn
noncomputable section
variable {F Pin : Type} [Field F]

def originalSourceRows (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor h ratio : ℕ) :=
  let W:=v.registeredFrom prior floor
  let u:=2^v.area.k*v.fundedWorkingUnit (v.argumentUnitFrom prior floor)
  ratio*W.headUnit*(W.signed.hosts*h+W.signed.hosts*W.signed.groups*(4*W.signedLayout.unit+u))

theorem original_source_paid_all (ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(Pin : Type),∀(v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor w J rate original : ℕ),
      let ext:=v.argumentUnitFrom prior floor
      let W:=v.registeredFrom prior floor
      let A:=v.registeredEntry prior floor
      let unit:=2^v.area.k*v.fundedWorkingUnit ext
      ∀(c : W.SignedChart) (capacity : prior.argumentsPerNode≤ v.vector.operands)
        (blocks : W.resolver.blocks=W.material.blocks),
      v.payload=h → W.signed=W.signedLayout.format h → 256≤ W.prior.placement.cap →
      2*W.fundedPanelUnit≤ h → 2*W.signedLayout.unit≤ h → 0<W.signed.hosts →
      0<v.venue.paidBits → v.venue.paidBits≤ v.area.unit → 4*v.fundedMaxUnit ext*2^v.area.k≤ h →
      J≤ Nat.log 2 h → 2^h≤ original → w+1≤ ratio*h →
      (∀i,W.ticketReadGeometry.coefficientInputs 32 unit i≤ scale J rate) →
      (W.originalSourcePhase floor w c A (v.registered_match prior floor capacity)
        (v.registered_geometry prior floor) blocks).wordInvoice≤
        v.originalReadCharge prior floor ratio J rate+v.originalSourceRows prior floor h ratio+
        2*(original/(2^J)^saving) :=by
  filter_upwards [head_transfer_paid_all (F:=F) ratio saving] with h transfer
  intro Pin v prior floor w J rate original extra W A unit c capacity blocks payload selected cap oldR newR live paid covers wide age size bus costs
  subst h
  have full:=v.original_source_charge prior floor w ratio c capacity blocks J rate selected cap oldR newR
    paid covers wide (by omega) costs
  have funding:=v.funded_argument_bounds extra (v.datedEntry prior floor) paid covers wide
  have laneCap : W.resolver.lanes≤ v.payload:=
    (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos v.area.k)).trans funding.outCap
  have used:=transfer Pin W floor w J original unit c rfl selected live newR funding.out
    laneCap funding.fill₂ age size bus
  have improve : (W.headTransferPhase floor c w).wordInvoice≤
       2*(original/(2^J)^saving)+v.originalSourceRows prior floor v.payload ratio:=
    (Nat.mul_le_mul_left _ (Nat.le_succ w)).trans used
  exact (full.trans (Nat.add_le_add_left improve _)).trans_eq (by omega)

theorem original_source_paid (ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor w J rate original : ℕ),
      let ext:=v.argumentUnitFrom prior floor
      let W:=v.registeredFrom prior floor
      let A:=v.registeredEntry prior floor
      let unit:=2^v.area.k*v.fundedWorkingUnit ext
      ∀(c : W.SignedChart) (capacity : prior.argumentsPerNode≤ v.vector.operands)
        (blocks : W.resolver.blocks=W.material.blocks),
      v.payload=h → W.signed=W.signedLayout.format h → 256≤ W.prior.placement.cap →
      2*W.fundedPanelUnit≤ h → 2*W.signedLayout.unit≤ h → 0<W.signed.hosts →
      0<v.venue.paidBits → v.venue.paidBits≤ v.area.unit → 4*v.fundedMaxUnit ext*2^v.area.k≤ h →
      J≤ Nat.log 2 h → 2^h≤ original → w+1≤ ratio*h →
      (∀i,W.ticketReadGeometry.coefficientInputs 32 unit i≤ scale J rate) →
      (W.originalSourcePhase floor w c A (v.registered_match prior floor capacity)
        (v.registered_geometry prior floor) blocks).wordInvoice≤
        v.originalReadCharge prior floor ratio J rate+v.originalSourceRows prior floor h ratio+
        2*(original/(2^J)^saving) :=
  (original_source_paid_all (F:=F) ratio saving).mono (fun _ all => all Pin)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
