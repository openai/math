import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Squared distances on a Euclidean page

The CAT(0) squared-distance inequality in Euclidean coordinates says that the
square of the distance function is strongly convex with Mathlib parameter two.
These lemmas pass its first-order bound to a limiting gradient at a facet.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Set Filter
open scoped RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {C : Set E} {f : E → ℝ} {x z p : E}

/-- Subtracting the Euclidean squared distance from the CAT(0) squared distance
leaves a convex function on the page, for every choice of origin. -/
theorem convexOn_sq_distance_sub_norm_sq
    (hcat : StrongConvexOn C 2 (fun v ↦ f v ^ 2)) (p : E) :
    ConvexOn ℝ C (fun v ↦ f v ^ 2 - ‖v - p‖ ^ 2) := by
  have h₀ : ConvexOn ℝ C (fun v ↦ f v ^ 2 - ‖v‖ ^ 2) := by
    simpa using strongConvexOn_iff_convex.mp hcat
  refine ⟨h₀.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := h₀.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h
  simp only [smul_eq_mul, norm_sub_sq_real, inner_add_left, real_inner_smul_left]
  nlinarith [congrArg (fun t : ℝ ↦ t * ‖p‖ ^ 2) hab]

variable [CompleteSpace E] {g : E}

/-- The support inequality for a differentiable convex function on a Euclidean page. -/
theorem convex_support_of_hasGradientAt
    (hf : ConvexOn ℝ C f) (hx : x ∈ C) (hg : HasGradientAt f g x) (hz : z ∈ C) :
    f x + ⟪g, z - x⟫ ≤ f z := by
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x z
  have hγ : HasFDerivAt f (InnerProductSpace.toDual ℝ E g) (γ 0) := by
    simpa [γ] using hg.hasFDerivAt
  have hline : HasDerivAt (f ∘ γ) ⟪g, z - x⟫ 0 :=
    hγ.comp_hasDerivAt 0 AffineMap.hasDerivAt_lineMap
  have h := (hf.comp_affineMap γ).le_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ γ ⁻¹' C by simpa [γ] using hx)
    (show (1 : ℝ) ∈ γ ⁻¹' C by simpa [γ] using hz) zero_lt_one hline
  simp [slope, γ] at h
  linarith

/-- The gradient of the convex correction to the squared distance. -/
theorem hasGradientAt_sq_distance_sub_norm_sq (hg : HasGradientAt f g x) (p : E) :
    HasGradientAt (fun v ↦ f v ^ 2 - ‖v - p‖ ^ 2)
      ((2 * f x) • g - (2 : ℝ) • (x - p)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (hg.hasFDerivAt.pow 2).sub (((hasFDerivAt_id x).sub_const p).norm_sq)
  convert! h using 1
  ext v
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

/-- First-order CAT(0) lower bound at a differentiability point in the page. -/
theorem sq_distance_support_of_hasGradientAt
    (hcat : StrongConvexOn C 2 (fun v ↦ f v ^ 2)) (hx : x ∈ C)
    (hg : HasGradientAt f g x) (hz : z ∈ C) :
    f x ^ 2 + 2 * f x * ⟪g, z - x⟫ + ‖z - x‖ ^ 2 ≤ f z ^ 2 := by
  have h := convex_support_of_hasGradientAt (convexOn_sq_distance_sub_norm_sq hcat x) hx
    (hasGradientAt_sq_distance_sub_norm_sq hg x) hz
  simpa [real_inner_smul_left, ← le_sub_iff_add_le] using h

/-- The squared cross-distance inequality at a facet, obtained by passing to
the limit in the support inequalities. Here `e` is the limiting gradient and
`r` the distance from the fixed point on the other page. -/
theorem sq_distance_support_of_tendsto_gradient
    (hcat : StrongConvexOn C 2 (fun v ↦ f v ^ 2)) {y g : ℕ → E} {e : E} {r : ℝ}
    (hy : ∀ n, y n ∈ C) (hd : ∀ n, HasGradientAt f (g n) (y n))
    (hyp : Tendsto y atTop (𝓝 p)) (hfr : Tendsto (fun n ↦ f (y n)) atTop (𝓝 r))
    (hge : Tendsto g atTop (𝓝 e)) (hz : z ∈ C) :
    r ^ 2 + 2 * r * ⟪e, z - p⟫ + ‖z - p‖ ^ 2 ≤ f z ^ 2 := by
  have hzsub : Tendsto (fun n ↦ z - y n) atTop (𝓝 (z - p)) := tendsto_const_nhds.sub hyp
  exact le_of_tendsto (((hfr.pow 2).add
    ((tendsto_const_nhds.mul hfr).mul (hge.inner hzsub))).add (hzsub.norm.pow 2))
    (Eventually.of_forall fun n ↦ sq_distance_support_of_hasGradientAt hcat (hy n) (hd n) hz)

end SpectralBooks
end LinearAlgebra
end OAI
