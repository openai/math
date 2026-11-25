import OAI.Hierarchy.DescentProfiledUniformCalendarRate
import OAI.Hierarchy.DescentProfiledUniformOrdinaryPrice
import OAI.Hierarchy.DescentProfiledUniformResetSpan

namespace OAI
/-! A single address exponent covers every genuine selected instruction before
the epoch tail, bus divisor, and physical machine word are chosen. -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledRate
open Chronology.RegisterTimeline
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g reset drift degreeMax : ℕ)

theorem uniform_addresses :
    ∃addr:ℕ,∀driftR slots,UniformAddresses G board op t f g reset drift degreeMax driftR slots addr :=
  uniform_addresses_of G board op t f g reset drift degreeMax
    (ProfiledOrdinaryOffer.uniform_ordinary_spans G board op t f g reset drift degreeMax)
    (ProfiledPosition.uniform_reset_spans G board op t f g reset drift degreeMax)

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledRate

end OAI
