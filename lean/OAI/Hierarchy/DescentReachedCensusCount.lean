import OAI.Hierarchy.DescentGroupStageData
import OAI.Hierarchy.DescentPackedHistoryMass
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The stored count of history records at a reached host, group and block -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSixParty DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k G H : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (groups : J≃Fin G) (hosts : V↪Fin H)

def count (b : ℕ) (h : Fin H) (g : Fin G) (x : Fin (2^k)) : Cell b :=
  if v : ∃u,hosts u=h then (PackedCensus.histories W A.pos A.block A.records (groups.symm g,v.choose) x:ℕ) else 0

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
