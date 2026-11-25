import OAI.Hierarchy.DescentStateBounds

namespace OAI
/-! # Whole-cable grain counts at a measured stage -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i : ℕ}

def grainCount (e : W.graph.Edge) := W.graph.width e/(A.z*G.b)

theorem grainCount_fit (ready : A.StateBounds S i) (e : W.graph.Edge) :
    W.graph.width e=A.grainCount e*(A.z*G.b) := (Nat.div_mul_cancel (ready.divides e)).symm

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
