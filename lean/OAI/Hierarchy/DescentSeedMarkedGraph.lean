import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentHubNetwork
import OAI.Hierarchy.CorrectionBatch

namespace OAI
/-! # Original marked copy graph and its immutable field table -/
namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing DescentSixParty Catalyst
open scoped Classical
noncomputable section
variable {F : Type*} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "P" => Fin (Fintype.card (Port p X.width))
def markedInput : MarkedWorld F 0 P (fun _=>1) :=
  let N := X.network.copyGraph
  ⟨⟨hubbed N,hubTables N X.network.copyTable⟩,
    Finset.univ.map (Function.Embedding.inl : N.Edge ↪ N.Edge⊕P)⟩

end
end Hierarchy.DescentInitialHost

end OAI
