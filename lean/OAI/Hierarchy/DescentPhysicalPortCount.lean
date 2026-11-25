import OAI.Hierarchy.CorrectionFrame

namespace OAI
/-! # Cardinality of the exterior ports on all independent copies -/
namespace Hierarchy.DescentSixParty
open Catalyst CorrectionFrame
open scoped Classical
variable {F : Type} [Field F]
omit [Field F] in
/-- Every catalyst or ordinary data pin occurs once on every independent copy. -/
theorem physical_port_count {k n : ℕ} (X : Approximation F k n) (d : ℕ) :
    Fintype.card (Port (d*n) (copiesWidth d X.width))=d*Fintype.card (Port n X.width) := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using
    (Fintype.card_congr (copiesPortEquiv (p:=n) d X.width)).symm

end Hierarchy.DescentSixParty

end OAI
