import OAI.Hierarchy.DescentOrdinaryBookMouthRate
import OAI.Hierarchy.DescentRegisteredArgumentScale
import OAI.Hierarchy.DescentSeedTokenWidths
import OAI.Hierarchy.DescentRegisteredTailCalendar
import OAI.Hierarchy.DescentOperandWidth

namespace OAI
/-! # One width for the actual stored book and the printed operand selectors -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook Chronology
open DescentDatedSeedStartup Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

def argumentMouthRate (t f g reset driftR : ℕ) :=
  mouthRate G t f g reset (initialDegreeMax t) driftR (3*OrdinaryBooks.bookMouthRate G t f g reset)
def argumentDigitRate (t f g reset driftR base : ℕ) :=
  13+argumentMouthRate G t f g reset driftR+(NativePitch.all_donor_rate G t f g reset).choose+
    (signedRates G t f g reset).amount+base

structure ArgumentCalendar (op : RotorSpec) (t f g reset τ B drift driftR degreeMax h : ℕ) : Prop where
  book : ∀fund i p degree seats (prior : DatePorts),
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset fund (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    let L:=OrdinaryBooks.atDate G S op g k i p (tail τ J) drift degree h seats prior
    p ≤ h → degree ≤ degreeMax → prior.nodes ≤ S.retainedNodes →
      prior.argumentsPerNode ≤ S.retainedArgumentsAt G drift → drift+1 ≤ scale J driftR →
      ∀j,L.bookMouthParameters j ≤ scale J (argumentMouthRate G t f g reset driftR)
  archive : ∀fund p degree : ℕ,
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset fund (tail τ J)
    let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
    p ≤ h → degree ≤ degreeMax → DescentOperandWidth.recordBits G S k (tail τ J) drift degree p ≤ scale J 3
  census : ∀fund last p i gain : ℕ,p≤h →
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset fund last
    let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
    S.censusBits p ≤ (DonorDate.atDate G S gain k i p).amount
  printed : ∀s Z : ℕ,Z ≤ s → s ≤ h → DescentPrimitivePalette.printedBits G s Z op ≤ scale (Nat.log 2 h/(2*B)) 3

theorem eventual_argument_width (op : RotorSpec) (t f g reset τ B drift driftR degreeMax : ℕ) (den : 0<B) :
    ∀ᶠ h : ℕ in atTop,ArgumentCalendar G op t f g reset τ B drift driftR degreeMax h :=by
  filter_upwards [OrdinaryBooks.all_mouth_fields_at G op t f g reset τ B drift driftR degreeMax den,
    DescentOperandWidth.issued G drift degreeMax t f g reset τ B den,
    census_fits_donor G t f g reset B den,DescentDatedSeedStartup.primitive_rate G op B den] with h book archive census printSize
  exact ⟨book,archive,census,fun s Z hz hs=>(printSize s Z hz hs).1⟩

end
end Hierarchy.DescentSixParty

end OAI
