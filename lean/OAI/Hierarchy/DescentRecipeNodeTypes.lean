import OAI.Hierarchy.DescentBitDescription
import OAI.Hierarchy.DescentNetworkWorld

namespace OAI
/-! The original marked-world bit description and its dependent type of physical recipe nodes. -/
namespace Hierarchy.DescentKernelHistory
open DescentSixParty Computability.BorderVNP.Crossing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

structure BitDescription (W : MarkedWorld F d P bits) where
  Tag : Type
  scalar : Tag→List (List Bool)→F
  recipe : SiteBits (U:=Tag) W.graph
  correct : ReadsBits W.graph scalar recipe W.tables

namespace NodeOrder
variable {U : Type} {D : ℕ}
def Global {N : Network D P bits} (r : SiteBits (U:=U) N) := Σ v : N.Site, (r v).Node

abbrev All {X : MarkedWorld F d P bits} (O : BitDescription X) := Global (N:=X.graph) O.recipe
end NodeOrder
end
end Hierarchy.DescentKernelHistory

end OAI
