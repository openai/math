import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! # Width of every physical edge in the initial copy graph -/
namespace Hierarchy.DescentInitialHost
open DescentSixParty Computability.BorderVNP.Crossing Catalyst
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {k p R s : ℕ} (X : Approximation F k p) (c : (initialGroup X R s).Choice)

theorem source_all_widths (e : ((initialGroup X R s).state c).graph.Edge) :
    ((initialGroup X R s).state c).graph.width e=s := by
  rcases e with ⟨i,e⟩
  change s*(hubbed X.network.copyGraph).width e=s
  exact (congrArg (s * ·)
    (hub_unit X.network.copyGraph (CorrectionBatch.physical_output X).1 e)).trans (Nat.mul_one s)

end
end Hierarchy.DescentInitialHost

end OAI
