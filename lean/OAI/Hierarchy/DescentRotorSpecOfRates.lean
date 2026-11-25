import OAI.Hierarchy.DescentRotorAlphabet
import OAI.Hierarchy.DescentResetRateData

namespace OAI
/-! # The literal rotor specification belonging to a genuine reset rate -/
namespace Hierarchy.DescentSixParty
open DescentCompiler
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {k : ℕ}

def RotorSpec.ofRates {D n h C f g cut tail} (r : ResetRates G S k D n h C f g cut tail) : RotorSpec :=
  ⟨n,r.board.arcs,C,r.bitsR,D,h,f,g⟩

end
end Hierarchy.DescentSixParty

end OAI
