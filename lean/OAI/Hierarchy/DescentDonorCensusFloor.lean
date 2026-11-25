import OAI.Hierarchy.DescentDonorCensusScale
import OAI.Hierarchy.DescentDateLaneAmount

namespace OAI
/-! # The authentic native matcher pitch accommodates the current signed census field -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The census precision is fixed by the calendar and original payload even on a rejected ballot. -/
theorem census_fits_donor (t f g reset B : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M tail p i gain : ℕ, p≤h →
        let S:=stageNumbers G t J f g reset M tail
        let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
        let date:=Chronology.DonorDate.atDate G S gain k i p
        S.censusBits p≤date.amount := by
  filter_upwards [census_donor_amount G t f g reset B positive] with h board
  dsimp only
  intro M tail p i gain used
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M tail
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  let date:=Chronology.DonorDate.atDate G S gain k i p
  change S.censusBits p≤date.amount
  exact board M tail p date.degree date.cap used

end Hierarchy.DescentCompiler.TerminalScale

end OAI
