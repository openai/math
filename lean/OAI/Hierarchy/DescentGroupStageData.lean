import OAI.Hierarchy.DescentStageMeasures
import OAI.Hierarchy.DescentCommonGroups
import OAI.Hierarchy.DescentSixPartyGadget
import OAI.Hierarchy.DescentHostDegree

namespace OAI
/-! # Physical coordinates and prices of a grouped compiler stage -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing DescentHostDirectory DescentColonies StarKeys
open scoped BigOperators Classical
noncomputable section
variable {P : Type} {d : ℕ} {bits : P→ℕ} {F : Type} [Field F]

/-- The current stages use a common site directory in every remaining group.
All expenditures below describe the incoming data, before any multiplier,
paint, selected pairs, or layout is chosen. -/
structure GroupStage (W : MarkedWorld F d P bits) (G : PoweredGadget F) (price ε : ℝ)
    (J V : Type) [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] (k : ℕ) where
  Atoms : Type
  wire : ℕ
  hist : ℕ
  z : ℕ
  cap : ℕ
  degree : ℕ
  pos : W.graph.Site→J×V
  block : W.graph.Site→Block k
  near : V→Finset V
  hub : V→Bool
  records : W.graph.Site→List Atoms
  fieldBits : 0<k
  degreeMin : 2≤degree
  degreeBound : ∀v,(near v).card≤degree
  symmetric : ∀v z,z∈near v ↔ v∈near z
  pricePos : 0<price
  wirePos : 0<wire
  unitPos : 0<z
  capPos : 0<cap
  small : ∀v i,blockMass W.graph pos block
    (W.siteUnits (fun u=>hub (pos u).2) records wire 256 hist) v i≤wire*(z*G.b)*cap
  saturated : ∀v,hub v.2=true→∀i,blockMass W.graph pos block
    (W.siteUnits (fun u=>hub (pos u).2) records wire 256 hist) v i=wire*(z*G.b)*cap
  noHubAtoms : ∀u,hub (pos u).2=true→ records u=[]
  peers : ∀e,pos (W.graph.dst e)∈groupedNear near (pos (W.graph.src e)) ∧
    pos (W.graph.src e)∈groupedNear near (pos (W.graph.dst e))
  same : ∀e,block (W.graph.src e)=block (W.graph.dst e)
  incidence : MarkedWorld.HubIncidence W (fun u=>hub (pos u).2)
  widths : ∀e∈W.core,W.graph.width e=z*G.b
  retained : (price*hist)*(∑u,((records u).length:ℝ))≤ε
  roots : ((Fintype.card J*Fintype.card V : ℕ):ℝ)*
    ((2:ℝ)^DescentHostDegree.packExponent 20 degree*(price*((wire*(z*G.b)*cap:ℕ):ℝ)))≤ε

end
end Hierarchy.DescentSixParty

end OAI
