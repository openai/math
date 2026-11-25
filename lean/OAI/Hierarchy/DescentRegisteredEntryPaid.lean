import OAI.Hierarchy.DescentRegisteredEntryCharge
import OAI.Hierarchy.DescentRegisteredOriginMouthFee
import OAI.Hierarchy.DescentChosenRegisteredDate

namespace OAI
/-! # All twelve registered ordinary argument phases on the single authentic ticket program -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open Filter DescentCompiler DescentDatedAddressBook DescentDatedOperandReadPipeline DescentCompiler.TerminalScale
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F]

def originMouthCharge (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor ratio J a : ℕ) :=
  let extra:=v.argumentUnitFrom prior floor
  let W:=v.registeredFrom prior floor
  let r:=(v.fundedClip extra).radix
  let u:=r*v.fundedWorkingUnit extra
  let H:=v.vector.hosts*v.vector.lows
  let h:=v.payload
  ratio*(2600*(v.vector.lows+1)*h+(160+300*r)*(H*h+H*v.vector.groups*u)+
    115*((4+r)*2^(h/2))*h+(109+115*((1+v.resolver.nodes*6)*(2*2^(h/2))))*h)+
    (ratio*scale J (20*a))*(h+(W.bornBook.hosts*h+W.bornBook.hosts*v.vector.groups*u)+2^(h/2)*h)

def argumentDateCharge (v : PhysicalOrdinary F Pin) (prior : DatePorts) (floor ratio J selectRate mouthRate : ℕ) :=
  v.registeredEntryCharge prior floor ratio+v.originalReadCharge prior floor ratio J selectRate+
    v.originalSourceRows prior floor v.payload ratio+v.originMouthCharge prior floor ratio J mouthRate

/-- The first summand is the actual retained seven-column and printed-role reader,
priced by the named trajectory's chosen registered resource proof. All remaining
summands are public numerical terms including both original-pitch shared lookups. -/
theorem registered_entry_paid_all (ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(Pin : Type),∀(v : PhysicalOrdinary F Pin) (prior : DatePorts)
      (floor w J a rate original : ℕ),
      let W:=v.registeredFrom prior floor
      let A:=v.registeredEntry prior floor
      let ext:=v.argumentUnitFrom prior floor
      let unit:=2^v.area.k*v.fundedWorkingUnit ext
      ∀(c : W.SignedChart) (capacity : prior.argumentsPerNode≤v.vector.operands)
        (blocks : W.resolver.blocks=W.material.blocks) (pg : Fin (7*W.vector.operands)),
      v.payload=h → W.signed=W.signedLayout.format h → 256≤W.prior.placement.cap →
      2*W.fundedPanelUnit≤h → 2*W.signedLayout.unit≤h → 0<W.signed.hosts →
      0<v.venue.paidBits → v.venue.paidBits≤v.area.unit → 4*v.fundedMaxUnit ext*2^v.area.k≤h →
      J≤Nat.log 2 h → 2^h≤original → w+1≤ratio*h → 2^v.area.k+1≤v.area.unit →
      (∀i,W.ticketReadGeometry.coefficientInputs 32 unit i≤ scale J rate) →
      W.bornBook.groups=W.vector.groups*W.vector.radix → (∀i,v.mouthParameters i≤ scale J a) →
      (A.population W floor).chunkBits≤h/4 → (A.population W floor).count≤2^(h/4) →
      (W.refChart floor).endAddress<2^w → ∀(fit : W.endAddress floor<2^w)
      (packed : W.resolver.lanes*DescentPackedOperand.unit W.resolver.size≤w/2)
      (chip : (A.chipBank W floor).Fits w (W.refsStart floor)),
      let mat:=v.registered_match prior floor capacity
      let shape:=v.registered_geometry prior floor
      let src:=W.nativeTicketExpr floor c A mat shape blocks
      let stage:=W.nativeTicketPreparation floor w c A mat shape blocks pg
      (W.argumentPhaseAfterSigned floor A mat src stage chip shape fit packed).wordInvoice≤
      W.inputFee A floor w+v.argumentDateCharge prior floor ratio J rate a+2*(original/(2^J)^saving) :=by
  filter_upwards [original_source_paid_all (F:=F) ratio saving] with h source
  intro Pin v prior floor w J a rate original W A ext unit c capacity blocks pg payload selected cap oldR newR live paid covered wide age initial bus matchPrice local_ groups mouthBounds chunks menu refs fit packed chip mat shape src stage
  subst h
  have wordBus : w≤ratio*v.payload:=by omega
  have native:=source Pin v prior floor w J rate original c capacity blocks rfl selected cap oldR newR live paid covered wide age initial bus local_
  have tail_:=v.registered_entry_charge prior floor w ratio c capacity blocks pg paid covered matchPrice wide
    wordBus chunks menu refs fit packed
  have front_:=v.registered_origin_mouth_bill prior floor capacity pg w ratio J a groups mouthBounds paid covered wide wordBus
  have front : (W.originAndMouth floor w A mat W.operandShortBits ((A.directory W floor mat).refs pg)).wordInvoice≤
      v.originMouthCharge prior floor ratio J a:=front_
  have seq : stage.wordInvoice=
      (W.originAndMouth floor w A mat W.operandShortBits ((A.directory W floor mat).refs pg)).wordInvoice+
        (W.originalSourcePhase floor w c A mat shape blocks).wordInvoice :=NativePhase.wordInvoice_seq ..
  change W.entryFee floor A mat src stage shape fit packed ≤
    v.registeredEntryCharge prior floor ratio + W.inputFee A floor w + stage.wordInvoice at tail_
  change (W.originalSourcePhase floor w c A mat shape blocks).wordInvoice ≤
    v.originalReadCharge prior floor ratio J rate + v.originalSourceRows prior floor v.payload ratio +
      2*(original/(2^J)^saving) at native
  rw [W.entry_word_fee floor A mat src stage chip shape fit packed]
  unfold argumentDateCharge
  omega

theorem registered_entry_paid (ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(v : PhysicalOrdinary F Pin) (prior : DatePorts)
      (floor w J a rate original : ℕ),
      let W:=v.registeredFrom prior floor
      let A:=v.registeredEntry prior floor
      let ext:=v.argumentUnitFrom prior floor
      let unit:=2^v.area.k*v.fundedWorkingUnit ext
      ∀(c : W.SignedChart) (capacity : prior.argumentsPerNode≤v.vector.operands)
        (blocks : W.resolver.blocks=W.material.blocks) (pg : Fin (7*W.vector.operands)),
      v.payload=h → W.signed=W.signedLayout.format h → 256≤W.prior.placement.cap →
      2*W.fundedPanelUnit≤h → 2*W.signedLayout.unit≤h → 0<W.signed.hosts →
      0<v.venue.paidBits → v.venue.paidBits≤v.area.unit → 4*v.fundedMaxUnit ext*2^v.area.k≤h →
      J≤Nat.log 2 h → 2^h≤original → w+1≤ratio*h → 2^v.area.k+1≤v.area.unit →
      (∀i,W.ticketReadGeometry.coefficientInputs 32 unit i≤ scale J rate) →
      W.bornBook.groups=W.vector.groups*W.vector.radix → (∀i,v.mouthParameters i≤ scale J a) →
      (A.population W floor).chunkBits≤h/4 → (A.population W floor).count≤2^(h/4) →
      (W.refChart floor).endAddress<2^w → ∀(fit : W.endAddress floor<2^w)
      (packed : W.resolver.lanes*DescentPackedOperand.unit W.resolver.size≤w/2)
      (chip : (A.chipBank W floor).Fits w (W.refsStart floor)),
      let mat:=v.registered_match prior floor capacity
      let shape:=v.registered_geometry prior floor
      let src:=W.nativeTicketExpr floor c A mat shape blocks
      let stage:=W.nativeTicketPreparation floor w c A mat shape blocks pg
      (W.argumentPhaseAfterSigned floor A mat src stage chip shape fit packed).wordInvoice≤
      W.inputFee A floor w+v.argumentDateCharge prior floor ratio J rate a+2*(original/(2^J)^saving) :=
  (registered_entry_paid_all (F:=F) ratio saving).mono (fun _ all => all Pin)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
