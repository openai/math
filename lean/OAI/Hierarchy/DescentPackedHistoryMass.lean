import OAI.Hierarchy.DescentStageMeasures

namespace OAI
/-! # History words at one original host and block -/
namespace Hierarchy.DescentSixParty.PackedCensus
open DescentColonies StarKeys
noncomputable section
variable {F P V A : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)

def histories (atoms : W.graph.Site→List A) (v : V) (x : Block k) :=
  blockMass W.graph pos ix (fun u=>(atoms u).length) v x

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
