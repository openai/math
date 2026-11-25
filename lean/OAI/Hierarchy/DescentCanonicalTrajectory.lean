import OAI.Hierarchy.DescentGLPhysicalTrajectory

namespace OAI
/-! # The first-index trajectory shared by issued resets and their native mixer -/
namespace Hierarchy.DescentGL.PhysicalTrajectory
open scoped Classical BigOperators
noncomputable section
variable {m : ℕ} (W : Fin (m+1) → Bits m → ℕ) (q : ℕ)

/-- Every memory placement uses the same sequence of first-minimizing rows. -/
def canonicalTrajectory : ℕ → Layout m :=
  (chosenRow_collisionTrajectory (LinearEquiv.refl _ _) (Weights W q)).choose

theorem canonicalTrajectory_chooses : Chooses (canonicalTrajectory W q) (Weights W q) := by
  intro i
  have step := (chosenRow_collisionTrajectory (LinearEquiv.refl _ _) (Weights W q)).choose_spec.2.1 i
  exact ⟨step.1,step.2.1⟩

theorem canonicalTrajectory_bound :
    allDepthCollisionCost (Weights W q) (canonicalTrajectory W q m) ≤
      (∑ T : Layout m, allDepthCollisionCost (Weights W q) T) / Fintype.card (Layout m) :=
  (chosenRow_collisionTrajectory (LinearEquiv.refl _ _) (Weights W q)).choose_spec.2.2

end
end Hierarchy.DescentGL.PhysicalTrajectory

end OAI
