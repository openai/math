import OAI.Hierarchy.DescentFixedHostGeometry
import OAI.Hierarchy.DescentRotorSpecOfRates

namespace OAI
namespace Hierarchy.DescentSixParty.EpochRotor.HostGeometry
open Catalyst
variable {F : Type} [Field F] {G : PoweredGadget F} {c : EpochRotor G} {τ β h M cp n : ℕ}
    {X : Approximation F cp n}

theorem spec (g : c.HostGeometry τ β h M X) : RotorSpec.ofRates g.reset=c.spec :=by
  simp only [RotorSpec.ofRates,EpochRotor.spec,g.board,g.bits]

theorem history (g : c.HostGeometry τ β h M X) :
    max 1 (max g.reset.bitsR (c.multiplicity*g.reset.bitsR)) =
      max 1 (max c.bits (c.multiplicity*c.bits)) :=by rw [g.bits]

end Hierarchy.DescentSixParty.EpochRotor.HostGeometry

end OAI
