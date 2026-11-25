import OAI.LinearAlgebra.SpectralBooks.Book.BookNormal
import OAI.LinearAlgebra.SpectralBooks.Facet

/-! # The cross-distance lower bound from the outward width increment

The limiting-gradient argument uses the normal-cone integral comparison
in the tangent model at the exterior differentiability points of the page.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open Book MeasureTheory Filter Set
open scoped InnerProductSpace Topology

/-- The normal-cone comparison in the book theorem implies the squared lower
bound on the distance to a point of normal height `r` on the other page. -/
theorem facet_sq_distance_of_outward_integral
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace (LiftSphere E)] [BorelSpace (LiftSphere E)]
    (σ : Measure (LiftSphere E)) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    {C K : Set E} {f : E → ℝ} {p e : E} {r : ℝ}
    (hlip : LipschitzOnWith 1 f C) (hc : ConvexOn ℝ C f)
    (hcat : StrongConvexOn C 2 (fun z ↦ f z ^ 2))
    (hp : p ∈ interior C) (hr : 0 < r) (hfp : f p = r) (he : ‖e‖ = 1)
    (hK : IsCompact K) (hbelow : ∀ z ∈ K, ⟪e, z - p⟫_ℝ ≤ 0)
    (hcmp : ∀ y ∈ interior C, 0 < ⟪y - p, e⟫_ℝ → 0 < f y → DifferentiableAt ℝ f y →
      ∫ n in normalCone K y, outwardWeight e n ∂σ ≤
      ∫ n in normalCone K y ∩ {n | ⟪(n : Lift E), liftedDirection (gradient f y) (f y)⟫_ℝ ≤ 0},
        outwardWeight e n ∂σ)
    (hfacet : ∀ v : E, ⟪v, e⟫_ℝ = 0 → ∀ᶠ t : ℝ in 𝓝 0, p + t • v ∈ C ∧
      f (p + t • v) = ‖(p + t • v) - (p + r • e)‖)
    {z : E} (hz : z ∈ C) :
    r ^ 2 + 2 * r * ⟪e, z - p⟫_ℝ + ‖z - p‖ ^ 2 ≤ f z ^ 2 := by
  apply facet_sq_distance_lower_bound hlip hc hcat hp hr hfp he _ hfacet hz
  intro y hy hout hpos hd
  have hg : ‖gradient f y‖ ≤ 1 := by
    simpa [gradient] using norm_fderiv_le_of_lipschitzOn ℝ (mem_interior_iff_mem_nhds.mp hy) hlip
  refine unit_gradient_of_outward_integral σ hK he hpos hg (fun w hw ↦ ?_)
    (hcmp y hy hout hpos hd)
  rw [real_inner_comm e (y - p), inner_sub_right] at hout
  have h := hbelow w hw
  rw [inner_sub_right] at h ⊢
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
