import OAI.LinearAlgebra.SpectralBooks.BookIndependence
import OAI.LinearAlgebra.SpectralBooks.Book.BookNormal
import OAI.LinearAlgebra.SpectralBooks.AngularWidth

/-!
# The two outward width increments

For a finite configuration containing the origin, dilating its old sites sends
the width increment for a new site to an integral on the normal cone.
Submodularity lets us include the additional tangent direction in this cone
when the contracted sites can be added at no cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace Book

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace Classical

section Width

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The limit of the width increment, integrated over the supporting directions. -/
def sphereMarginal [MeasurableSpace (Metric.sphere (0 : V) 1)]
    (σ : Measure (Metric.sphere (0 : V) 1)) (S : Finset V) (v : V) : ℝ :=
  ∫ n in Subtype.val ⁻¹' normalConeAtZero S, max 0 ⟪(n : V), v⟫_ℝ ∂σ

/-- Adjoining a direction cuts the old supporting normals by its hemisphere. -/
theorem sphereMarginal_insert [MeasurableSpace (Metric.sphere (0 : V) 1)]
    (σ : Measure (Metric.sphere (0 : V) 1)) (S : Finset V) (v X : V) :
    sphereMarginal σ (insert X S) v =
      ∫ n in (Subtype.val ⁻¹' normalConeAtZero S) ∩ {n | ⟪(n : V), X⟫_ℝ ≤ 0},
        max 0 ⟪(n : V), v⟫_ℝ ∂σ := by
  have heq : (Subtype.val : Metric.sphere (0 : V) 1 → V) ⁻¹' normalConeAtZero (insert X S) =
      (Subtype.val ⁻¹' normalConeAtZero S) ∩ {n | ⟪(n : V), X⟫_ℝ ≤ 0} := by
    ext n
    simp [normalConeAtZero, and_comm]
  simp only [sphereMarginal, heq]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The finite width difference from adjoining `v` to `a • S`. -/
def widthIncrement (S : Finset V) (hS : S.Nonempty) (v : V) (a : ℝ) : ℝ :=
  meanWidth (insert v (S.image (a • ·))) (Finset.insert_nonempty _ _) -
    meanWidth (S.image (a • ·)) (hS.image _)

omit [BorelSpace V] in
/-- Rescaling about the occupied origin identifies the right difference quotient
with a width increment at reciprocal dilation. -/
theorem widthIncrement_inv (S : Finset V) (hS : S.Nonempty) (v : V) {h : ℝ}
    (hh : 0 < h) :
    (meanWidth (insert (h • v) S) (Finset.insert_nonempty _ _) - meanWidth S hS) / h =
      widthIncrement S hS v h⁻¹ := by
  have heq := meanWidth_smul (insert (h • v) S) (Finset.insert_nonempty _ _)
    (inv_nonneg.mpr hh.le)
  simp only [Finset.image_insert, inv_smul_smul₀ hh.ne'] at heq
  rw [widthIncrement, heq, meanWidth_smul S hS (inv_nonneg.mpr hh.le)]
  ring

/-- Equation `eq:width-marginal` for the manuscript's normalized sphere measure. -/
theorem tendsto_widthIncrement_sphere (b : Metric.sphere (0 : V) 1) {S : Finset V}
    (h0 : 0 ∈ S) (v : V) :
    Tendsto (widthIncrement S ⟨0, h0⟩ v) atTop (𝓝 (sphereMarginal (widthSphereMeasure b) S v)) := by
  have hl := tendsto_meanWidth_insert_smul_sub h0 v
  rw [gaussian_normalConeIntegral_eq_sphereIntegral b S v] at hl
  unfold widthIncrement
  simpa only [sphereMarginal, max_comm (0 : ℝ)] using hl

/-- Independence removes the point on the other page from the old diagonal.
The old flat then gives the first width increment. The contracted configurations
`A M i` have the tangent width as their rescaled limit. Together with
submodularity and enclosure of these sites at no cost, these facts imply the
comparison of normal-cone integrals in the book proof. -/
theorem sphereMarginal_le_with_tangent (b : Metric.sphere (0 : V) 1) {α ι : Type*} [DecidableEq α]
    (δ : Finset α → ℝ) (hsub : IntersectingSubmodular δ)
    (hmono : ∀ ⦃S T⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    {l : Filter ι} [l.NeBot] (h : ι → ℝ) (hh : Tendsto h l (𝓝[>] 0))
    (P : Finset α) (z : ι → α) (A : ℝ → ι → Finset α)
    {S : Finset V} (h0 : 0 ∈ S) (v X : V)
    (hflat : ∀ᶠ i in l, δ (insert (z i) P) - δ P =
      meanWidth (insert (h i • v) S) (Finset.insert_nonempty _ _) -
        meanWidth S ⟨0, h0⟩)
    (hadd : ∀ M > 0, ∀ᶠ i in l, (A M i).Nonempty ∧ δ (P ∪ A M i) = δ P)
    (htangent : ∀ M > 0, Tendsto (fun i => (δ (insert (z i) (A M i)) - δ (A M i)) / h i)
      l (𝓝 (widthIncrement (insert X S) (Finset.insert_nonempty _ _) v M))) :
    sphereMarginal (widthSphereMeasure b) S v ≤ sphereMarginal (widthSphereMeasure b) (insert X S) v := by
  have hlim : Tendsto (fun i => (δ (insert (z i) P) - δ P) / h i) l
      (𝓝 (sphereMarginal (widthSphereMeasure b) S v)) := by
    apply ((tendsto_widthIncrement_sphere b h0 v).comp (tendsto_inv_nhdsGT_zero.comp hh)).congr'
    filter_upwards [hflat, hh.eventually self_mem_nhdsWithin] with i hi hh'
    rw [hi]
    exact (widthIncrement_inv S ⟨0, h0⟩ v hh').symm
  apply ge_of_tendsto (tendsto_widthIncrement_sphere b (Finset.mem_insert_of_mem h0) v)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
  apply le_of_tendsto_of_tendsto hlim (htangent M hM)
  filter_upwards [hadd M hM, hh.eventually self_mem_nhdsWithin] with i hi hi0
  apply div_le_div_of_nonneg_right _ (le_of_lt (show 0 < h i from hi0))
  have hinc := intersectingSubmodular_union_increment hsub hmono hi.1
    (Finset.subset_union_right (s₁ := P)) {z i}
  have hpinc := hmono (Finset.insert_nonempty (z i) P)
    (Finset.insert_subset_insert (z i) (Finset.subset_union_left (s₂ := A M i)))
  simp only [Finset.union_singleton, hi.2] at hinc
  linarith

end Width

section CornerCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The occupied origin and the centered corners of the common cube. -/
def centeredCorners (C : Finset E) (y : E) : Finset (Lift E) :=
  insert 0 (C.image fun z => horizontal (z - y))

omit [InnerProductSpace ℝ E] in
theorem zero_mem_centeredCorners (C : Finset E) (y : E) : 0 ∈ centeredCorners C y :=
  Finset.mem_insert_self _ _

/-- Passing to the convex hull preserves the supporting normal directions. -/
theorem normalCone_convexHull (C : Set E) (y : E) :
    normalCone (convexHull ℝ C) y = normalCone C y := by
  ext n
  constructor
  · exact fun h z hz => h z (subset_convexHull ℝ C hz)
  · intro hn z hz
    let u := (n : Lift E).fst
    have hf (x : E) : ⟪(n : Lift E), horizontal (x - y)⟫_ℝ = ⟪u, x⟫_ℝ - ⟪u, y⟫_ℝ := by
      simp [horizontal, u, inner_sub_right]
    rw [hf, sub_nonpos]
    apply convexHull_min (t := {x | ⟪u, x⟫_ℝ ≤ ⟪u, y⟫_ℝ}) _ _ hz
    · intro w hw
      exact sub_nonpos.mp ((hf w) ▸ (hn w hw))
    · exact convex_halfSpace_le (.mk (fun a b => inner_add_right _ _ _)
        (fun r a => real_inner_smul_right _ _ _)) _

theorem centeredCorners_normalCone (C : Finset E) (y : E) :
    (Subtype.val : LiftSphere E → Lift E) ⁻¹' normalConeAtZero (centeredCorners C y) =
      normalCone (convexHull ℝ (C : Set E)) y := by
  rw [normalCone_convexHull]
  ext n
  simp [normalConeAtZero, centeredCorners, normalCone]

/-- The finite configuration after adding the opposite-page tangent vector
has the old normal cone intersected with one more closed hemisphere. -/
theorem centeredCorners_normalCone_insert (C : Finset E) (y : E) (X : Lift E) :
    (Subtype.val : LiftSphere E → Lift E) ⁻¹' normalConeAtZero (insert X (centeredCorners C y)) =
      normalCone (convexHull ℝ (C : Set E)) y ∩ {n | ⟪(n : Lift E), X⟫_ℝ ≤ 0} := by
  rw [← centeredCorners_normalCone]
  ext n
  simp [normalConeAtZero, and_comm]

/-- At an exterior point of the common cube, the comparison for its finite
corner configurations implies the unit-gradient and sign conclusions used at
the facet. The cube can be any polytope presented by its finite corner set. -/
theorem unit_gradient_of_corner_marginal
    [FiniteDimensional ℝ E] [MeasurableSpace (LiftSphere E)] [BorelSpace (LiftSphere E)]
    (σ : Measure (LiftSphere E)) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (C : Finset E) {y e g : E} {r : ℝ} (he : ‖e‖ = 1) (hr : 0 < r) (hg : ‖g‖ ≤ 1)
    (hbelow : ∀ z ∈ C, ⟪e, z - y⟫_ℝ < 0)
    (hcmp : sphereMarginal σ (centeredCorners C y) (horizontal e) ≤
      sphereMarginal σ (insert (liftedDirection g r) (centeredCorners C y)) (horizontal e)) :
    ‖g‖ = 1 ∧ 0 ≤ ⟪e, g⟫_ℝ := by
  apply unit_gradient_of_outward_integral σ C.finite_toSet.isCompact he hr hg hbelow
  simpa only [sphereMarginal, centeredCorners_normalCone, centeredCorners_normalCone_insert,
    normalCone_convexHull, outwardWeight] using hcmp

end CornerCone

end Book

end

end SpectralBooks
end LinearAlgebra
end OAI
