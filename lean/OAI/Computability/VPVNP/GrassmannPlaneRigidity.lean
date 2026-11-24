import OAI.Computability.VPVNP.GrassmannFrameRigidity
import OAI.Computability.VPVNP.GrassmannFrameDimensions
import OAI.Computability.VPVNP.GrassmannMoveSquare

/-!
# Equality rigidity for two completed block spans

Opposite-side equality on every Grassmann square of type `(r, 1)` determines
the value of a pair observable on every ordered pair presented by a frame
of two independent blocks of size `r` with a common completion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

open Function

/-- Opposite sides of type `r` in equality squares force the same value for
all ordered frame presentations of type `r < m`. -/
theorem frame_planes_rigid {m r s : ℕ} (hr : r < m) (hm : s + r = m)
    (D : Plane m → Plane m → ℝ)
    (opp : ∀ a b c d, IsSquare r 1 a b c d → D a b = D d c)
    {v v' : Fin (r + r) → Space m} {w w' : Fin s → Space m}
    (h : LinearIndependent (ZMod 2) (Sum.elim v w))
    (h' : LinearIndependent (ZMod 2) (Sum.elim v' w')) :
    D (leftPlane v w hm h) (rightPlane v w hm h) =
      D (leftPlane v' w' hm h') (rightPlane v' w' hm h') := by
  classical
  let E (U V : Submodule (ZMod 2) (Space m)) :=
    if hU : Module.finrank (ZMod 2) U = m then
      if hV : Module.finrank (ZMod 2) V = m then D ⟨U, hU⟩ ⟨V, hV⟩ else 0
    else 0
  have eval (a b : Plane m) : E a.val b.val = D a b := by
    simp only [E, dite_eq_left a.property, dite_eq_left b.property]
    rfl
  rw [← eval, ← eval (leftPlane v' w' hm h') (rightPlane v' w' hm h')]
  apply completed_blocks_rigid (K := ZMod 2) (A := leftIndices r) (B := rightIndices r)
    (by omega) (by simp only [Module.finrank_pi, Fintype.card_fin]; omega) E _ h h'
  intro u t i x hi
  obtain ⟨a, b, c, d, ha, hb, hc, hd, sq⟩ := completion_move_square hm i hi
  rw [← ha, ← hb, ← hc, ← hd, eval, eval]
  exact opp a b c d sq

end Grassmann

end VPVNP
end Computability
end OAI
