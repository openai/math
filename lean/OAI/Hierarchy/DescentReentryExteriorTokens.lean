import OAI.Hierarchy.DescentResetExteriorTokens
import OAI.Hierarchy.DescentReentryGroupStage
import OAI.Hierarchy.DescentOrderedReentryBasic
import OAI.Hierarchy.DescentPiecesSiteUnits

namespace OAI
namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentResetAttachments DescentRouterBank MarkedWorld Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d h C Ht L : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {q ε : ℝ} (Z : ResetInput A q ε h C Ht) (T : Z.Terminals)
local notation "W" => Z.reenter T

theorem reentry_exterior_balance (hubs : A.HubExterior Z.hub) : (W).HubExterior (Z.reentryTag T) := by
  apply installed_hub_balance
  rwa [show T.hub ∘ T.home=Z.hub from funext T.tag]

open private Hierarchy.DescentResetTrunks.namedHub from OAI.Hierarchy.DescentReentryLoad in
omit [Fintype P] in
theorem reentry_exterior_owners (owns : ∀x,Z.hub (A.graph.attach x)=true) (pin : P) :
    Z.reentryTag T ((W).graph.attach pin)=true := by
  change Hierarchy.DescentResetTrunks.namedHub T.hub (Z.resetNames T ((W).graph.attach pin))=true
  rw [Z.read_source_pin T pin]
  exact (T.tag _).trans (owns pin)

theorem ordinary_exterior_balance (hubs : A.HubExterior Z.hub) : (Z.ordinaryWorld T).HubExterior (Z.reentryTag T) := by
  intro v active
  exact (MarkedWorld.pieces_siteUnits (W) Z.unit _ (Z.counts_fit T)
    (Z.reentryTag T) (fun _ => ([] : List Unit)) 1 256 0 v).trans
    (Z.reentry_exterior_balance T hubs v active)

theorem ordered_exterior_balance (hubs : A.HubExterior Z.hub) (key : A.graph.Edge↪Fin L) :
    (Z.orderedReentry T key).HubExterior (Z.reentryTag T) :=
  Z.reentry_exterior_balance T hubs

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
