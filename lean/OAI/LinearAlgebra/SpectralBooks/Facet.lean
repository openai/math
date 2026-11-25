import OAI.LinearAlgebra.SpectralBooks.FacetApproach
import OAI.LinearAlgebra.SpectralBooks.SquaredDistance
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

/-! # The limiting gradient on the common facet

At a point in the relative interior of the common facet, the distance function
restricts to the Euclidean distance from a point at positive normal height.
This identifies each unit outward-facing limiting subgradient with the normal.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Filter Set
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : Set E} {f : E → ℝ} {p e g : E} {r : ℝ}

/-- A subgradient of the distance function at a relative interior point of the
facet annihilates each tangent direction. The neighborhood hypothesis says that
the two charts agree on the facet and that the indicated line stays in it locally. -/
theorem facet_tangential_inner_eq_zero (hr : 0 < r) (he : ‖e‖ = 1)
    (hsupp : ∀ z ∈ C, r + ⟪g, z - p⟫_ℝ ≤ f z)
    {v : E} (hv : ⟪v, e⟫_ℝ = 0)
    (hfacet : ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ C ∧
      f (p + t • v) = ‖(p + t • v) - (p + r • e)‖) :
    ⟪g, v⟫_ℝ = 0 := by
  let c := ⟪g, v⟫_ℝ
  have hpos : ∀ᶠ t : ℝ in 𝓝 0, 0 < r + t * c :=
    (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul continuous_const))).mem_nhds
      (by simpa using hr)
  let Q := fun t : ℝ ↦ t ^ 2 * (‖v‖ ^ 2 - c ^ 2) - t * (2 * r * c)
  have hmin : IsLocalMin Q 0 := by
    filter_upwards [hfacet, hpos] with t ht hrt
    have h := hsupp _ ht.1
    rw [ht.2, add_sub_cancel_left, add_sub_add_left_eq_sub, real_inner_smul_right] at h
    have hsq := pow_le_pow_left₀ hrt.le h 2
    rw [norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right, hv,
      norm_smul, norm_smul, he] at hsq
    simp only [Real.norm_eq_abs, mul_one, mul_zero, sub_zero, mul_pow, sq_abs] at hsq
    change Q 0 ≤ Q t
    dsimp [Q]
    dsimp [c] at *
    nlinarith
  have hQ : HasDerivAt Q (-(2 * r * c)) 0 := by
    dsimp [Q]
    convert! ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖v‖ ^ 2 - c ^ 2)).sub
      ((hasDerivAt_id (0 : ℝ)).mul_const (2 * r * c))) using 1
    simp
  have h := hmin.hasDerivAt_eq_zero hQ
  change c = 0
  rcases mul_eq_zero.mp (by linarith : 2 * r * c = 0) with hzero | hzero
  · nlinarith
  · exact hzero

/-- A unit vector orthogonal to all tangent directions and pointing outwards
is the outward unit normal. -/
theorem eq_normal_of_unit_tangential_zero (hg : ‖g‖ = 1) (he : ‖e‖ = 1)
    (hge : 0 ≤ ⟪g, e⟫_ℝ) (htan : ∀ v : E, ⟪v, e⟫_ℝ = 0 → ⟪g, v⟫_ℝ = 0) :
    g = e := by
  have hproj : ⟪g - ⟪g, e⟫_ℝ • e, e⟫_ℝ = 0 := by
    simp [inner_sub_left, real_inner_smul_left, he]
  have ht := htan _ hproj
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hg] at ht
  have hone : ⟪g, e⟫_ℝ = 1 := by nlinarith
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := norm_sub_sq_real g e
  rw [hg, he, hone] at h
  nlinarith [norm_nonneg (g - e)]

/-- If all gradients along a sequence approaching the relative interior of
the facet are unit and have nonnegative normal component, they converge to the
outward unit normal. -/
theorem facet_gradient_tendsto_normal [FiniteDimensional ℝ E] {y G : ℕ → E}
    (hr : 0 < r) (he : ‖e‖ = 1)
    (hy : Tendsto y atTop (𝓝 p)) (hf : Tendsto (fun j ↦ f (y j)) atTop (𝓝 r))
    (hunit : ∀ j, ‖G j‖ = 1) (hout : ∀ j, 0 ≤ ⟪G j, e⟫_ℝ)
    (hsupp : ∀ j z, z ∈ C → f (y j) + ⟪G j, z - y j⟫_ℝ ≤ f z)
    (hfacet : ∀ v : E, ⟪v, e⟫_ℝ = 0 → ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ C ∧
      f (p + t • v) = ‖(p + t • v) - (p + r • e)‖) :
    Tendsto G atTop (𝓝 e) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨g, hg, ms, hms, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    (x := fun k ↦ G (ns k)) (fun k ↦ by simpa [Metric.mem_sphere] using hunit (ns k))
  have hge : 0 ≤ ⟪g, e⟫_ℝ := le_of_tendsto_of_tendsto' tendsto_const_nhds
    (hlim.inner tendsto_const_nhds) (fun k ↦ hout (ns (ms k)))
  have hs : ∀ z ∈ C, r + ⟪g, z - p⟫_ℝ ≤ f z := by
    intro z hz
    have hsub := hns.comp hms.tendsto_atTop
    exact le_of_tendsto_of_tendsto' ((hf.comp hsub).add
      (hlim.inner (tendsto_const_nhds.sub (hy.comp hsub)))) tendsto_const_nhds
      (fun k ↦ hsupp (ns (ms k)) z hz)
  have heq := eq_normal_of_unit_tangential_zero (by simpa [Metric.mem_sphere] using hg)
    he hge (fun v hv ↦ facet_tangential_inner_eq_zero hr he hs hv (hfacet v hv))
  exact ⟨ms, heq ▸ hlim⟩

/-- Equation (book-cross-distance), using the gradient information at the
outward differentiability points. Rademacher's theorem supplies the sequence,
and the strong convexity inequality is the CAT(0) squared-distance bound in
the Euclidean chart. -/
theorem facet_sq_distance_lower_bound [FiniteDimensional ℝ E]
    (hlip : LipschitzOnWith 1 f C) (hc : ConvexOn ℝ C f)
    (hcat : StrongConvexOn C 2 (fun z ↦ f z ^ 2))
    (hp : p ∈ interior C) (hr : 0 < r) (hfp : f p = r) (he : ‖e‖ = 1)
    (hout : ∀ y ∈ interior C, 0 < ⟪y - p, e⟫_ℝ → 0 < f y →
      DifferentiableAt ℝ f y → ‖gradient f y‖ = 1 ∧ 0 ≤ ⟪e, gradient f y⟫_ℝ)
    (hfacet : ∀ v : E, ⟪v, e⟫_ℝ = 0 → ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ C ∧
      f (p + t • v) = ‖(p + t • v) - (p + r • e)‖)
    {z : E} (hz : z ∈ C) :
    r ^ 2 + 2 * r * ⟪e, z - p⟫_ℝ + ‖z - p‖ ^ 2 ≤ f z ^ 2 := by
  obtain ⟨y, hy, hyj⟩ := exists_differentiable_seq_above_facet hlip hp (hfp ▸ hr) he
  have hym j := interior_subset (hyj j).1
  have hd j := (hyj j).2.2.2.hasGradientAt
  have hf : Tendsto (fun j ↦ f (y j)) atTop (𝓝 r) := by
    rw [← hfp]
    exact (hlip.continuousOn _ (interior_subset hp)).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hy, Eventually.of_forall hym⟩)
  have hgrad j := hout _ (hyj j).1 (hyj j).2.1 (hyj j).2.2.1 (hyj j).2.2.2
  apply sq_distance_support_of_tendsto_gradient hcat hym hd hy hf _ hz
  exact facet_gradient_tendsto_normal hr he hy hf (fun j ↦ (hgrad j).1)
    (fun j ↦ by simpa only [real_inner_comm (gradient f (y j)) e] using (hgrad j).2)
    (fun j _ h ↦ convex_support_of_hasGradientAt hc (hym j) (hd j) h) hfacet

end SpectralBooks
end LinearAlgebra
end OAI
