import OAI.Computability.VPVNP.GrassmannRigidityFrames
import OAI.Hierarchy.GrassmannTransitivity

namespace OAI
namespace Computability.VPVNP.Grassmann.Rigidity

/-- At equality in every type-`(r,1)` quadrilateral, the value on an ordered pair
equals the mean over the entire Grassmann distance class. -/
theorem distance_eq_mean {m r : ℕ} (hr : r < m) (D : Plane m → Plane m → ℝ)
    (symm : ∀ a b, D a b = D b a)
    (opposite : ∀ a b c d, IsSquare r 1 a b c d → D a b = D c d)
    (p : Pair m r) : D p.val.1 p.val.2 = mean D r :=
  distance_eq_mean_of_transitive Hierarchy.GrassmannTransitivity.pair_transitive
    hr D symm opposite p

end Computability.VPVNP.Grassmann.Rigidity

end OAI
