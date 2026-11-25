import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI
/-! # The orbit of a nonzero binary difference under invertible layouts -/

namespace Hierarchy.DescentGL

/-- An isomorphism between the two lines taking their designated generators
to one another extends to an invertible layout on the whole binary space. -/
theorem exists_map {k : ℕ} {x y : Fin k → ZMod 2} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ L : (Fin k → ZMod 2) ≃ₗ[ZMod 2] (Fin k → ZMod 2), L x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin k → ZMod 2) x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin k → ZMod 2) y hy
  obtain ⟨L, hL⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨L, ?_⟩
  have eqn := hL (ex 1)
  change ((ey (ex.symm (ex 1))).val : Fin k → ZMod 2) = L (ex 1).val at eqn
  rw [ex.symm_apply_apply] at eqn
  simpa [ex, ey] using eqn.symm


end Hierarchy.DescentGL

end OAI
