import OAI.Hierarchy.DescentReturnRateNumbers
import OAI.Hierarchy.DescentOrdinaryPeerWordTariff

namespace OAI
/-! # The uniform prefix rate for the actual bounded hub expression -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

abbrev returnPrice :=returnPriceWith DescentOrdinaryVenueReturn.hubOp
theorem return_rates (G : PoweredGadget F) (t f gain reset : ℕ) :
    ∃rate : ℕ,∀J D cap : ℕ,D≤ maximumDegree t →
      cap≤2^(8+capRate G t gain*((t+1)*J)) →
      let k:=groupBits t J (hostRate t reset) (capRate G t gain) (cutRate t f gain)
      let growth:=2*(2^hostRate t reset*2^k)
      let oldUnit:=scale J (donorRates G t f gain reset).amount
      let newUnit:=scale J (signedRates G t f gain reset).amount
      returnPrice D (2^k) cap growth oldUnit newUnit (scale J (materialRate G t f gain reset))
        (scale J (signedRates G t f gain reset).controls) ≤ scale J rate :=
  return_rates_with DescentOrdinaryVenueReturn.hubOp G t f gain reset

def returnRate (G : PoweredGadget F) (t f g reset : ℕ) := (return_rates G t f g reset).choose

end
end Hierarchy.DescentSixParty.Chronology

end OAI
