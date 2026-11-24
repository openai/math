import OAI.Computability.VPVNP.CompressionProcedure
import OAI.Computability.VPVNP.CompressionTemplates

/-!
# Running the fixed refresh template

The refresh at the end of a block consumes the port-index coordinates and
restores the degree from the last exponent in the chosen schedule. Its
energy error uses only the fixed refresh template.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open MotifConversion Refresh DegreeRefresh

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

/-- The refresh coefficient in (7.3) uses only the initial degree, graph
degree and common Poincaré bound. -/
noncomputable def refreshProcedure :
    Procedure R S.portExponent (S.degreeExponent 0) S.portExponent 1
      (refreshMultiplier S.baseDegree (2 ^ S.expanderExponent) S.poincare) := by
  let hdH := Nat.two_pow_pos S.expanderExponent
  let conn := (S.port_bound.connected_and_pos S.port_order).1
  let hd := S.degree_bounds.2
  let hk := (B.solution_iff f).mp hf |>.2
  let g (n : ℕ) (X : State S.portExponent (S.portExponent + n)) :=
    dyadicRefreshPass X S.graph hdH conn B.refresh S.port_order hd (f ∘ Sum.inr) hk
  have hgain : 0 ≤ refreshMultiplier S.baseDegree (2 ^ S.expanderExponent) S.poincare := by
    change 0 ≤ (S.baseDegree : ℝ) + 2 * (S.portComparison + 1)
    positivity [S.portComparison_pos]
  refine Procedure.ofPass (κ := 1) one_pos hgain (le_max_left 0 B.refresh.energyConstant)
    g ?_ ?_
  · intro n X i
    rw [one_mul]
    exact (dyadicRefreshNext_positions X S.graph hdH conn B.refresh S.port_order hd i).symm
  · intro n X i
    have h := dyadicRefreshNext_energy X S.graph hdH conn B.refresh S.port_order hd
      (show 0 ≤ S.portComparison + 1 by linarith [S.portComparison_pos]) i
    exact h.trans (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_right 0 _)
      (sq_nonneg (X.positions : ℝ))) _)

/-- The additive bound precedes the assignment of the parameter values. -/
@[simp] theorem refreshProcedure_error :
    (B.refreshProcedure f hf).error = max 0 B.refresh.energyConstant := rfl

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
