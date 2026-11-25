import OAI.Hierarchy.DescentDatedWOriginPrice
import OAI.Hierarchy.DescentDatedMouthBounds
import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentOrdinaryDatedEntry
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! Price the stamped origin and newborn mouth on the registered date at its actual W address. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentStaticWordColumn
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (prior : DatePorts) (floor : ℕ)
local notation "extra_" => v.argumentUnitFrom prior floor
local notation "W_" => v.registeredFrom prior floor
local notation "A_" => v.registeredEntry prior floor

/-- The first phase of nativeTicketPreparation is paid on the same mounted directory
that supplies every operand of the following five selectors. -/
theorem registered_origin_mouth_bill (capacity : prior.argumentsPerNode≤v.vector.operands)
    (pg : Fin (W_).vector.pageCount) (w ratio J a : ℕ)
    (grouping : (W_).bornBook.groups=(W_).vector.groups*(W_).vector.radix)
    (bounds : ∀i,v.mouthParameters i≤ scale J a)
    (paid : 0<v.venue.paidBits) (input : v.venue.paidBits≤v.area.unit)
    (room : 4*v.fundedMaxUnit extra_*2^v.area.k≤v.payload) (bus : w≤ratio*v.payload) :
    let mat:=v.registered_match prior floor capacity
    let src:=((A_).directory W_ floor mat).refs pg
    let r:=(v.fundedClip extra_).radix
    let u:=r*v.fundedWorkingUnit extra_
    let H:=v.vector.hosts*v.vector.lows
    let h:=v.payload
    ((W_).originAndMouth floor w A_ mat (W_).operandShortBits src).wordInvoice ≤
      ratio*(2600*(v.vector.lows+1)*h+(160+300*r)*(H*h+H*v.vector.groups*u)+
        115*((4+r)*2^(h/2))*h+(109+115*((1+v.resolver.nodes*6)*(2*2^(h/2))))*h)+
      (ratio*scale J (20*a))*(h+((W_).bornBook.hosts*h+(W_).bornBook.hosts*v.vector.groups*u)+2^(h/2)*h) :=by
  intro mat src r u H h
  let entry:=v.datedEntry prior floor
  let funded : PhysicalOrdinary F P:={v with ingressWords:=(W_).ingressWords,origin:=⟨(W_).origin.preparationWords⟩}
  have selection : (W_).originChart.peak≤ extra_ :=
    (v.argumentWidth_le entry extra_ 11).trans (Nat.le_max_left ..)
  have short : v.mouthPeak extra_≤ extra_ :=
    (v.mouth_purchase extra_ entry).trans (Nat.le_max_left ..)
  have first:=funded.funded_w_origin_at extra_ ((W_).refsStart floor)
    ((A_).directory W_ floor mat) pg floor (W_).operandShortBits w ratio selection paid input room bus
  have second:=funded.funded_mouth_at_scale extra_ floor w ratio J a A_ mat grouping bounds short paid input room bus
  change (((W_).originPrefix floor (W_).operandShortBits w src).seq ((W_).originPrefixMouth floor w A_ mat)).wordInvoice ≤ _
  rw [NativePhase.wordInvoice_seq]
  exact Nat.add_le_add first second

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
