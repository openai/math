import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.Rademacher

/-! # Norming by derivatives of the norm

The derivative of a norm at any nonzero differentiability point also occurs
at the normalization of that point. In finite dimension these derivatives
approximate the norm of every vector from below.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Real


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivatives of the norm at its differentiable unit vectors. -/
def smoothNormDerivatives (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (E →L[ℝ] ℝ) :=
  {f | ∃ x : E, ‖x‖ = 1 ∧ HasFDerivAt (fun z : E => ‖z‖) f x}

theorem smoothNormDerivatives_norm_le_one {f : E →L[ℝ] ℝ}
    (hf : f ∈ smoothNormDerivatives E) : ‖f‖ ≤ 1 := by
  obtain ⟨x, _, hx⟩ := hf
  rw [← hx.fderiv]
  exact NNReal.coe_one ▸ norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := E))

theorem exists_smoothNormDerivative_gt [FiniteDimensional ℝ E] [Nontrivial E]
    (v : E) {r : ℝ} (hr : r < ‖v‖) :
    ∃ f ∈ smoothNormDerivatives E, r < f v := by
  obtain ⟨x, hxv, hx⟩ := Metric.dense_iff.mp (dense_differentiableAt_norm (E := E))
    v ((‖v‖ - r) / 2) (by linarith)
  change DifferentiableAt ℝ (fun z : E => ‖z‖) x at hx
  have hx0 : x ≠ 0 := fun h => not_differentiableAt_norm_zero E (h ▸ hx)
  let f := fderiv ℝ (fun z : E => ‖z‖) x
  have hmem : f ∈ smoothNormDerivatives E :=
    ⟨‖x‖⁻¹ • x, norm_smul_inv_norm (𝕜 := ℝ) hx0,
      hx.hasFDerivAt.hasFDerivAt_norm_smul_pos (inv_pos.mpr (norm_pos_iff.mpr hx0))⟩
  refine ⟨f, hmem, ?_⟩
  have hdiff : f (x - v) ≤ ‖x - v‖ := calc
    f (x - v) ≤ ‖f (x - v)‖ := le_norm_self _
    _ ≤ ‖f‖ * ‖x - v‖ := f.le_opNorm _
    _ ≤ 1 * ‖x - v‖ := by gcongr; exact smoothNormDerivatives_norm_le_one hmem
    _ = ‖x - v‖ := one_mul _
  rw [map_sub, show f x = ‖x‖ from hx.fderiv_norm_self] at hdiff
  rw [Metric.mem_ball, dist_eq_norm] at hxv
  have htri := norm_sub_norm_le v x
  rw [norm_sub_rev] at htri
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
