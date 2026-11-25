import OAI.Hierarchy.DescentRecipeNodeTypes
import OAI.Hierarchy.DescentBundleHistory

namespace OAI
/-! # The physical interval shape of each original local recipe -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentKernelHistory
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}
structure WorldShape (p R : ℕ) {W : MarkedWorld F d P bits} (B : BitDescription W) where
  sites : ∀v,Shape p (B.recipe v)
  stride : ∀v u j g,((sites v).chunk u j g).stride≤R
  edges : ∀e,p∣W.graph.width e

end Hierarchy.DescentBundleHistory

end OAI
