import OAI.Hierarchy.PriceRays
import OAI.Hierarchy.RecessionSlope
import OAI.LinearAlgebra.SpectralBooks.PriceBlowup

namespace OAI
/-! # A homogeneous system of prices on a Euclidean spectral flat -/

namespace Hierarchy

open Filter LinearAlgebra.SpectralBooks
open scoped Topology
noncomputable section

variable {F : Type*} [Field F] {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (P : SpectralPlacementPrices F E)

private theorem translate_price {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F)
    (x : I → E) (v : E) : P.price T (fun i => x i + v) = P.price T x := by
  let c : I → E := fun _ => v
  have path (t : ℝ) : t • c + x = fun i => x i + t • v := by
    funext i
    exact add_comm (t • v) (x i)
  have bound (t : ℝ) : P.price T (t • c + x) ≤ ∑ i, ‖x i‖ * Real.logb 2 (Fintype.card (T.Leg i)) := by
    rw [path]
    exact price_translate_bound P T x (t • v)
  have equal := convex_bdd_eq (convex_price_line P T x c) bound
  change P.price T ((1 : ℝ) • c + x) = P.price T ((0 : ℝ) • c + x) at equal
  rw [path 1, zero_smul, zero_add] at equal
  simpa only [one_smul] using equal

private def scale (t : ℝ) := max 1 t

private theorem scale_pos (t : ℝ) : 0 < scale t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

private theorem scaled_dist (p q : E) :
    Tendsto (fun t => dist (scale t • p) (scale t • q) / scale t)
      ((Ultrafilter.of (atTop : Filter ℝ)) : Filter ℝ) (𝓝 (dist p q)) := by
  simpa only [dist_smul₀, Real.norm_of_nonneg (scale_pos _).le,
    mul_div_cancel_left₀ _ (scale_pos _).ne'] using
    (tendsto_const_nhds (x := dist p q) :
      Tendsto (fun _ : ℝ => dist p q) ((Ultrafilter.of (atTop : Filter ℝ)) : Filter ℝ) (𝓝 (dist p q)))

/-- All rescaled evaluations use one compactness limit, so their normalized spectra
and their values on overlapping finite sets stay compatible. -/
private def rayPrices (H : SpectralPlacementPrices F E) : SpectralPlacementPrices F E :=
  H.blowup (Ultrafilter.of (atTop : Filter ℝ)) scale scale_pos (fun t x => scale t • x) 0 scaled_dist

private theorem ray_limit {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F) (x : I → E) :
    Tendsto (fun t : ℝ => P.price T (t • x) / t) atTop (𝓝 ((rayPrices P).price T x)) := by
  let U := Ultrafilter.of (atTop : Filter ℝ)
  have convex : ConvexOn ℝ Set.univ (fun t : ℝ => P.price T (t • x)) := by
    simpa only [add_zero] using convex_price_line P T 0 x
  have zero : P.price T ((0 : ℝ) • x) = 0 := by
    rw [zero_smul]
    convert P.collapsed T (0 : E) using 2
  obtain ⟨L, hl⟩ := exists_recession_slope convex zero (price_ray_bound P T x)
  have eqn : (fun t : ℝ => P.price T (scale t • x) / scale t) =ᶠ[atTop]
      (fun t : ℝ => P.price T (t • x) / t) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    simp only [scale, max_eq_right ht]
  have target := SpectralPlacementPrices.tendsto_blowupFamily_price (fun _ : ℝ => P) U
    scale scale_pos (fun t y => scale t • y) 0 scaled_dist T x
  have actual : Tendsto (fun t : ℝ => P.price T (scale t • x) / scale t)
      (U : Filter ℝ) (𝓝 L) := ((tendsto_congr' eqn).mpr hl).mono_left (Ultrafilter.of_le _)
  have identify : L = (rayPrices P).price T x := tendsto_nhds_unique actual target
  rwa [← identify]

/-- The homogeneous-flat lemma, obtained by taking the limiting slope of each
tensor price on a ray. -/
theorem homogeneousFlat_of_flat (h : HasSpectralFlat F d) : Nonempty (HomogeneousFlat F d) := by
  obtain ⟨P⟩ := h
  let Q := rayPrices P
  refine ⟨⟨Q, translate_price Q, Q.convexOn_price, ?_⟩⟩
  intro I _ T x r hr
  have ht : Tendsto (fun t : ℝ => t*r) atTop atTop :=
    (tendsto_mul_const_atTop_of_pos hr).mpr tendsto_id
  have right := ((ray_limit P T x).comp ht).const_mul r
  apply tendsto_nhds_unique (ray_limit P T (r • x))
  apply right.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht'
  change r * (P.price T ((t*r) • x) / (t*r)) = P.price T (t • r • x) / t
  rw [smul_smul]
  field_simp

theorem allHomogeneousFlats_of_flats (flats : ∀ d : ℕ, 0 < d → HasSpectralFlat F d) :
    AllHomogeneousFlats F := fun d hd => homogeneousFlat_of_flat (flats d hd)

end
end Hierarchy

end OAI
