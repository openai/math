import OAI.Computability.BorderVNP.ShortenEpochTangent
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Local crossings in products of hyperbolic planes

The metric is the square root of the sum of squared hyperbolic component
distances. The product chart does not increase any wire cost. At scale
`s` the distance from the image of a terminal to its specified unit-speed
geodesic is at most `η * s` for all directions simultaneously. These facts
let a single sufficiently small radius work for all the direction bins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open scoped ENNReal

variable {I : Type*} [Fintype I]

/-- The product of upper half-planes in the paper's Riemannian product metric. -/
abbrev HyperbolicHost (I : Type*) := PiLp 2 fun _ : I => UpperHalfPlane

/-- Spatial tangent coordinates in the product host. -/
noncomputable def productChart (v : PiLp 2 fun _ : I => ℂ) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => tangentChart (v i)

/-- Squared product distance is the sum of the squared hyperbolic factor distances. -/
theorem host_dist_sq (v w : HyperbolicHost I) :
    dist v w ^ 2 = ∑ i, dist (v i) (w i) ^ 2 := by
  rw [PiLp.dist_eq_sum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- The product chart contracts the lengths of all wires, including internal
control and selector cables of the fixed gadget. -/
theorem productChart_dist_le (v w : PiLp 2 fun _ : I => ℂ) :
    dist (productChart v) (productChart w) ≤ dist v w := by
  rw [← sq_le_sq₀ dist_nonneg dist_nonneg, host_dist_sq, PiLp.dist_sq_eq_of_L2]
  exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ dist_nonneg (dist_tangentChart_le (v i) (w i)) 2

/-- The angular direction of a complex vector, with a fixed unit representative at zero. -/
noncomputable def unitDirection (z : ℂ) : ℂ :=
  if z = 0 then 1 else ‖z‖⁻¹ • z

/-- Every angular representative is a unit vector. -/
theorem unitDirection_norm (z : ℂ) : ‖unitDirection z‖ = 1 := by
  by_cases hz : z = 0
  · simp [unitDirection, hz]
  · simp [unitDirection, hz]

/-- Restoring the component speed recovers the original tangent vector. -/
theorem norm_smul_unitDirection (z : ℂ) : ‖z‖ • unitDirection z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [unitDirection, hz]

/-- Follow a straight geodesic in each factor at its component speed. -/
noncomputable def productLine (v : PiLp 2 fun _ : I => ℂ) (t : ℝ) : HyperbolicHost I :=
  WithLp.toLp 2 fun i => tangentLine (unitDirection (v i)) (t * ‖v i‖)

/-- Product geodesic distance is exactly elapsed parameter times tangent speed. -/
theorem dist_productLine (v : PiLp 2 fun _ : I => ℂ) (r s : ℝ) :
    dist (productLine v r) (productLine v s) = |r - s| * ‖v‖ := by
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))).mp
  rw [host_dist_sq, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show dist (productLine v r i) (productLine v s i) =
      |r * ‖v i‖ - s * ‖v i‖| from dist_tangentLine _ (unitDirection_norm _) _ _,
    ← sub_mul, abs_mul, abs_of_nonneg (norm_nonneg _), mul_pow]

/-- Uniform terminal hooks for arbitrary unit tangent directions in the full
product, including directions with vanishing components. -/
theorem uniform_product_hooks {η : ℝ} (hη : 0 < η) :
    ∃ h > 0, ∀ s ∈ Set.Icc (0 : ℝ) h, ∀ v : PiLp 2 (fun _ : I => ℂ), ‖v‖ ≤ 1 →
      dist (productChart (s • v)) (productLine v s) ≤ η * s := by
  obtain ⟨h, hh, hhook⟩ := uniform_tangent_hooks hη
  refine ⟨h, hh, ?_⟩
  intro s hs v hv
  have hηs := mul_nonneg hη.le hs.1
  rw [← sq_le_sq₀ dist_nonneg hηs, host_dist_sq]
  calc
    _ ≤ ∑ i, ((η*s) * ‖v i‖)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ dist_nonneg
      have hi := (PiLp.norm_apply_le v i).trans hv
      have hrad : s * ‖v i‖ ∈ Set.Icc (0 : ℝ) h :=
        ⟨mul_nonneg hs.1 (norm_nonneg _), (mul_le_of_le_one_right hs.1 hi).trans hs.2⟩
      have hpt : (s * ‖v i‖) • unitDirection (v i) = s • v i := by
        rw [mul_smul, norm_smul_unitDirection]
      change dist (tangentChart (s • v i)) (tangentLine (unitDirection (v i)) (s * ‖v i‖)) ≤ _
      simpa only [hpt, ← mul_assoc] using
        hhook _ hrad _ (unitDirection_norm (v i))
    _ = (η*s)^2 * ‖v‖^2 := by simp_rw [mul_pow, ← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) hv 2) (sq_nonneg (η*s))

end Epoch

end BorderVNP
end Computability
end OAI
