import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# First variation in a flat triangle

To compare the first variations of two squared distances, use the triangle
inequality at positive parameters and then pass to the right-hand limit at zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open Filter Topology

/-- For two distances initially equal to `L` and `s * L`, the triangle
inequality with third side `(1 - s) * L` orders their normalized first
variations. The two witnesses may be chosen separately for every parameter. -/
theorem flatTriangle_firstVariation {L s k k' H2 : ℝ} (hL : 0 < L) (hs : 0 < s)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      x ^ 2 = L ^ 2 + t * k + t ^ 2 * H2 ∧
      y ^ 2 ≤ (s * L) ^ 2 + t * k' + t ^ 2 * H2 ∧ x ≤ (1 - s) * L + y) :
    s * k ≤ k' := by
  let d := 2 * (s * L)
  have hd : 0 < d := by dsimp [d]; positivity
  let v := fun t : ℝ ↦ k' + t * H2
  have bound (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) :
      d ^ 2 * (k + t * H2) ≤ 2 * d * L * v t + t * (v t) ^ 2 := by
    obtain ⟨x, y, hx, _, hxSq, hySq, hxy⟩ := h t ht ht'
    have hy : d * y ≤ d * (s * L) + t * v t := by
      dsimp [d, v]
      nlinarith only [hySq, sq_nonneg (y - s * L)]
    have hx' : d * x ≤ d * L + t * v t := by
      have hxy' := mul_le_mul_of_nonneg_left hxy hd.le
      linarith only [hy, show d * x ≤ d * L - d * (s * L) + d * y by
        convert hxy' using 1; ring]
    have hsq := pow_le_pow_left₀ (mul_nonneg hd.le hx) hx' 2
    rw [mul_pow, hxSq] at hsq
    apply le_of_mul_le_mul_left _ ht
    nlinarith only [hsq]
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      d ^ 2 * (k + t * H2) ≤ 2 * d * L * v t + t * (v t) ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)]
      with t ht ht'
    exact bound t ht ht'.le
  have hc₁ : Continuous (fun t : ℝ ↦ d ^ 2 * (k + t * H2)) := by fun_prop
  have hc₂ : Continuous (fun t : ℝ ↦ 2 * d * L * v t + t * (v t) ^ 2) := by dsimp [v]; fun_prop
  have hzero := le_of_tendsto_of_tendsto hc₁.continuousWithinAt.tendsto
    hc₂.continuousWithinAt.tendsto he
  simp only [zero_mul, add_zero, v] at hzero
  apply le_of_mul_le_mul_left (a := 2 * d * L) _ (by positivity)
  dsimp [d] at hzero ⊢
  nlinarith only [hzero]

end SpectralGeometry

end VPVNP
end Computability
end OAI
