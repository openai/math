import OAI.Hierarchy.DescentStateBounds
import OAI.Hierarchy.DescentGroupSiteOrder
import OAI.Hierarchy.DescentGraphPairing

namespace OAI
/-! # Physically named ordinary stage reached along a branch -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentHostDegree DescentHostDirectory DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

/-- All branches share the number of live groups and the uniform per-epoch
grain. Their actual common host vertex sets can depend on past choices. -/
structure Reached (W : MarkedWorld F d P bits) (G : PoweredGadget F) (q ε : ℝ)
    (S : AtomSchedule) (k age z degree wire hist : ℕ) where
  V : Type
  [finite : Fintype V]
  [eqV : DecidableEq V]
  placement : GroupStage W G q ε (Fin (S.groupCount age)) V k
  valid : placement.StateBounds S age
  grain : placement.z=z
  edges : placement.wire=wire
  atoms : placement.hist=hist
  branch : placement.degree=degree
  order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)
  vertex : V↪Fin (Fintype.card V)
  edgeName : 0<age → ∀e,DescentPacking.originalId W.graph.Edge e=(order e).val
  siteName : 0<age → ∀v,DescentPacking.originalId W.graph.Site v=(placement.site vertex valid.coordinates v).val

attribute [instance] Reached.finite Reached.eqV

end
end Hierarchy.DescentSixParty

end OAI
