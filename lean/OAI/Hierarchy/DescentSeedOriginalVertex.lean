import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.BitNetwork.CopyGraph

namespace OAI
/-! # The original vertices in a seed network -/
namespace Hierarchy.DescentSeedRoot
open Catalyst
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
abbrev Old := X.network.copyGraph.Site
end Hierarchy.DescentSeedRoot

end OAI
