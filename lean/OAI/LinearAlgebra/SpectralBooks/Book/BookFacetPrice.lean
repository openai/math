import OAI.LinearAlgebra.SpectralBooks.Book.BookPriceFlat
import OAI.LinearAlgebra.SpectralBooks.FacetChart

/-!
# Outward comparison for a doubled cube

The old increment is computed in page coordinates, and contracted placements
have limiting prices in the tangent hull. These data give the normal-cone
inequality required by the cross-distance theorem.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Book

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace Classical

variable {X : Type*}

private theorem evaluate_insert_congr {V A : Type*}
    (f : (T : Finset V) → T.Nonempty → A) {d₁ d₂ : DecidableEq V} {v : V} {T : Finset V}
    {h₁ : (@insert V _ (@Finset.instInsert V d₁) v T).Nonempty}
    {h₂ : (@insert V _ (@Finset.instInsert V d₂) v T).Nonempty} :
    f (@insert V _ (@Finset.instInsert V d₁) v T) h₁ =
      f (@insert V _ (@Finset.instInsert V d₂) v T) h₂ := by
  cases Subsingleton.elim d₁ d₂
  rfl

section Chart

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

set_option maxHeartbeats 700000 in
/-- At each exterior differentiability point, the tangent price is the limiting
price of the configurations at fractions `hM`, divided by `h`. The flat page
law, corner independence and the segment property then yield
`FacetOutwardComparison` for the chart's distance to the fixed opposite point. -/
theorem facetOutwardComparison_of_contracted_prices [MetricSpace X]
    (δ : Finset X → ℝ) (γ : X → X → ℝ → X) (c : E → X) (x : X) (i : ι)
    (b : LiftSphere E)
    (hsub : IntersectingSubmodular δ)
    (hmono : ∀ ⦃S T : Finset X⦄, S.Nonempty → S ⊆ T → δ S ≤ δ T)
    (hseg : ∀ (T : Finset X) (u v : X), u ∈ T → v ∈ T → ∀ t ∈ Icc (0 : ℝ) 1,
      δ (insert (γ u v t) T) = δ T)
    (hflat : ∀ T : Finset E, ∀ hT : T.Nonempty, (T : Set E) ⊆ coordinateCube ι 2 →
      δ (T.image c) = meanWidth T hT)
    (k : ℝ) (hind : ∀ T : Finset E, coordinateCubeCorners ι 1 ⊆ T →
      (T : Set E) ⊆ coordinateCube ι 2 → δ (insert x (T.image c)) = δ (T.image c) + k)
    {J : Type*} {l : Filter J} [l.NeBot] (h : J → ℝ) (hh : Tendsto h l (𝓝[>] 0))
    (htangent : ∀ y ∈ interior (coordinateCube ι 2), 1 < y i → 0 < dist (c y) x →
      DifferentiableAt ℝ (fun w => dist (c w) x) y → ∀ M > 0,
      let e := EuclideanSpace.single i (1 : ℝ)
      let P := oldConfiguration c x (coordinateCubeCorners ι 1) y
      let Xy := liftedDirection (gradient (fun w => dist (c w) x) y) (dist (c y) x)
      let S := insert Xy (centeredCorners (coordinateCubeCorners ι 1) y)
      Tendsto (fun j =>
        let A := contractedSites γ (c y) P (h j * M)
        (δ (insert (c (y + h j • e)) A) - δ A) / h j) l
        (𝓝 (widthIncrement S (Finset.insert_nonempty _ _) (horizontal e) M))) :
    FacetOutwardComparison (widthSphereMeasure b) i (fun w => dist (c w) x) := by
  intro y hy hyi hpos hdiff
  let C := coordinateCubeCorners ι 1
  let e := EuclideanSpace.single i (1 : ℝ)
  let P := oldConfiguration c x C y
  let Xy := liftedDirection (gradient (fun w => dist (c w) x) y) (dist (c y) x)
  have hC : (C : Set E) ⊆ coordinateCube ι 2 := by
    refine Subset.trans ?_ (coordinateCube_one_subset_interior_two.trans interior_subset)
    rw [← convexHull_coordinateCubeCorners (ι := ι) (show 0 ≤ (1 : ℝ) by norm_num)]
    exact subset_convexHull _ _
  have hh0 : Tendsto h l (𝓝 0) := (tendsto_nhdsWithin_iff.mp hh).1
  have hfn : Tendsto (fun j => y + h j • e) l (𝓝 y) := by
    simpa using (tendsto_const_nhds (x := y)).add (hh0.smul (tendsto_const_nhds (x := e)))
  have hlimit := sphereMarginal_le_with_tangent b δ hsub hmono h hh P
    (fun j => c (y + h j • e)) (fun M j => contractedSites γ (c y) P (h j * M))
    (S := centeredCorners C y) (zero_mem_centeredCorners C y) (horizontal e) Xy
    (by
      filter_upwards [hfn (mem_interior_iff_mem_nhds.mp hy)] with j hz
      refine (price_increment_on_old_page δ c x C k hC hflat hind y e (h j)
        (interior_subset hy) hz).trans ?_
      apply congrArg (· - meanWidth (centeredCorners C y) ⟨0, zero_mem_centeredCorners C y⟩)
      exact evaluate_insert_congr (fun T hT => meanWidth T hT))
    (by
      intro M hM
      have hprod : Tendsto (fun j => h j * M) l (𝓝 0) := by
        simpa using hh0.mul_const M
      filter_upwards [hprod (Iio_mem_nhds (zero_lt_one' ℝ)), hh.eventually self_mem_nhdsWithin]
        with j hj hp
      refine ⟨Finset.insert_nonempty _ _, price_union_contractedSites δ γ hseg _ ?_
        ⟨mul_nonneg (le_of_lt (show 0 < h j from hp)) hM.le, le_of_lt hj⟩⟩
      simp [P, oldConfiguration])
    (by
      intro M hM
      have hl := htangent y hy hyi hpos hdiff M hM
      convert hl using 2
      exact evaluate_insert_congr (fun T hT => widthIncrement T hT (horizontal e) M))
  rw [sphereMarginal_insert] at hlimit
  simpa only [sphereMarginal, centeredCorners_normalCone, C,
    convexHull_coordinateCubeCorners (zero_le_one' ℝ), outwardWeight, Xy, e] using hlimit

end Chart
end Book

end

end SpectralBooks
end LinearAlgebra
end OAI
