import OAI.Hierarchy.DescentPrivateDonorUniform
import OAI.Hierarchy.DescentCalendarNumbers
import OAI.Hierarchy.DescentMaximumDegreeQuota

namespace OAI
/-! # Actual uniform prices used by the original donor calendar -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

/-- One common compiler choice of exponents controls memory packing and time. -/
structure DonorRates (G : PoweredGadget F) (t f g reset : ℕ) where
  work : ℕ
  amount : ℕ
  bounds : ∀J D cap : ℕ,D≤maximumDegree t→cap≤2^(8+capRate G t g*((t+1)*J))→
    let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
    donorGrade (2^k) D cap≤ scale J work ∧ donorAmount k D cap G.b G.C G.k≤ scale J amount

def donorRates (G : PoweredGadget F) (t f g reset : ℕ) : DonorRates G t f g reset := by
  have sizes:=donor_uniform t (hostRate t reset) (capRate G t g) (cutRate t f g) (maximumDegree t) G.b G.C G.k
  exact ⟨sizes.choose,sizes.choose_spec.choose,sizes.choose_spec.choose_spec⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
