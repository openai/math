import OAI.Hierarchy.GrassmannGap
import OAI.Hierarchy.GrassmannExpanders

namespace OAI
/-! # The nonlinear expander theorem for a uniformly excluded cube -/

namespace Hierarchy.NonlinearExpanders

open Computability.VPVNP.Grassmann

/-- For each uniformly excluded cube, one bounded-degree expander family works for all the
complete CAT(0) targets in the class. -/
theorem excluded_cube : ExcludedCubeTheorem := by
  intro d hd ε hε I X instM instC hcat hex
  let m := d + 1
  have hm : 2 ≤ m := by dsimp [m]; omega
  obtain ⟨η,hη,hgap⟩ := grassmann_gap (m := m) (Nat.lt_succ_self d) hε X hcat hex
  let b := max 0 ((m : ℝ) - η)
  have hb : 0 ≤ b := le_max_left _ _
  have hbm : b < m := max_lt (by exact_mod_cast (show 0 < m by omega)) (by linarith)
  apply expanders_of_grassmann_gap hm hb hbm X hcat
  intro i x
  exact (hgap i x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (mean_nonneg (fun a b => sq_nonneg (dist (x a) (x b))) 1))


end Hierarchy.NonlinearExpanders

end OAI
