import OAI.Hierarchy.DescentReturnUnitRate
import OAI.Hierarchy.DescentOrdinaryTailShapeRate
import OAI.Hierarchy.DescentSignedRateNumbers
import OAI.Hierarchy.DescentCalibratedIncomingVolume
import OAI.Hierarchy.DescentDonorCensusFloor

namespace OAI
/-! # One public calibration for every selected ordinary return and all its successor rows -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup DescentDatedAddressBook Chronology
open DescentPacking.PackedMatch.Local.Stage.Dated Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
def incomingRate (t f g reset : ℕ) := (NativePitch.dated_volume G t f g reset).choose
def returnLaneRate (t f g reset funds : ℕ) :=
  tailUnitRate (groupRate G t f g reset+funds) (signedRates G t f g reset).amount (incomingRate G t f g reset)
def returnDateRate (t f g reset driftR funds : ℕ) :=
  endRate (tailLayoutRate G t f g reset driftR (returnLaneRate G t f g reset funds))

structure ReturnCalendar (t f g reset driftR funds τ B ratio h : ℕ) : Prop where
  width : 2*scale (Nat.log 2 h/(2*B)) (returnLaneRate G t f g reset funds)≤h
  census : ∀M tail p i gain : ℕ,p≤h →
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset M tail
    let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
    S.censusBits p≤(DonorDate.atDate G S gain k i p).amount
  rows : ∀M p i H : ℕ,
    let J:=Nat.log 2 h/(2*B)
    let S:=stageNumbers G t J f g reset M (tail τ J)
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    ∀ordinary:ℕ→Ordinary,p≤h →
      (∀j<S.length,j%(S.rounds+1)≠S.rounds→
        (ordinary j).payload=h ∧ (ordinary j).unit=(DonorDate.atDate G S g k j p).amount) →
      let m:=NativePitch.incoming S k (tail τ J) p f h ordinary i
      0< m ∧ m≤h/2 ∧ H*chunks (S.groupCount i) m*h≤H*h+H*S.groupCount i*scale J (incomingRate G t f g reset)
  paid : ∀J M last i fee : ℕ,J≤Nat.log 2 h → 2^h≤2*M →
    let S:=stageNumbers G t J f g reset M last
    let R:=ratio*scale J (returnDateRate G t f g reset driftR funds)
    fee≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) h →
      fee≤S.hostSize i*h*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R

/-- The three public purchases use the same original word height and group-count calendar. -/
theorem eventual_registered_tail (t f g reset driftR funds τ B ratio saving : ℕ) (op : RotorSpec) (drift : ℕ)
    (selection : incomingRate G t f g reset+2≤B) (slack : returnLaneRate G t f g reset funds<B)
    (branch : G.b≤2^(capRate G t g))
    (endFit : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h : ℕ in atTop,ReturnCalendar G t f g reset driftR funds τ B ratio h :=by
  have positive : 0<B:=by omega
  have inputs:=(NativePitch.dated_volume G t f g reset).choose_spec op drift τ B selection branch endFit
  filter_upwards [AgeBound.payload_room _ B slack,census_fits_donor G t f g reset B positive,inputs,
    scheduled_tail_funding G t f g reset ratio (tailLayoutRate G t f g reset driftR (returnLaneRate G t f g reset funds)) saving]
    with h word census rows pages
  exact ⟨word,census,rows,pages⟩

end
end Hierarchy.DescentSixParty

end OAI
