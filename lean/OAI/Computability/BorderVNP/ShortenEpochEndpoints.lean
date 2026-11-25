import OAI.Computability.BorderVNP.ShortenEpochPlacement
import OAI.Computability.BorderVNP.ShortenEpochBins

/-!
# Endpoint tolerance inside direction and position bins

For either orientation of a segment, two configurations in the same bin
give close terminal points. The proof uses the uniform hook estimate
between the spatial hyperboloid chart and the true geodesic, followed by
uniform continuity of the chart on the compact lifted configuration set.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Metric Set MeasureTheory

variable {I : Type*} [Fintype I]

omit [Fintype I] in
/-- The placed chart varies continuously with both the center and the tangent
coordinate. This uses Mathlib's product and hyperbolic topologies. -/
theorem continuous_placed_chart :
    Continuous (fun cv : HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) =>
      shiftTo cv.1 (productChart cv.2)) := by
  have hc : Continuous tangentChart := (LipschitzWith.of_dist_le_mul (K := 1)
    (fun v w => by simpa using dist_tangentChart_le v w)).continuous
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  have hcenter := (PiLp.continuous_apply (p := 2) (β := fun _ : I => UpperHalfPlane) i).comp
    (continuous_fst (Y := PiLp 2 fun _ : I => ℂ))
  have hcoord := hc.comp ((PiLp.continuous_apply (p := 2) (β := fun _ : I => ℂ) i).comp
    (continuous_snd (X := HyperbolicHost I)))
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun cv : HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) =>
    ((cv.1 i).re : ℂ) + (cv.1 i).im • ((tangentChart (cv.2 i) : UpperHalfPlane) : ℂ))
  exact (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp hcenter)).add
    ((UpperHalfPlane.continuous_im.comp hcenter).smul (UpperHalfPlane.continuous_coe.comp hcoord))

/-- At every positive, sufficiently small scale one can choose null-frontier
bins so that both true endpoints of each oriented segment are within
`η * s` of the corresponding endpoints of its representative, including
zero-speed surface components. -/
theorem exists_endpointBins {G X : Type*} [Group G] [Fintype G] [PseudoMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (μ : Measure X) [SFinite μ] [SMulInvariantMeasure G X μ] {S : Set X} (hS : IsCompact S)
    (center : X → HyperbolicHost I) (v : X → PiLp 2 (fun _ : I => ℂ))
    (hc : ContinuousOn center S) (hv : ContinuousOn v S) (hunit : ∀ x ∈ S, ‖v x‖ ≤ 1)
    {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (hhook : ∀ d : PiLp 2 (fun _ : I => ℂ), ‖d‖ ≤ 1 →
      dist (productChart (s • d)) (productLine d s) ≤ η/3*s) :
    ∃ bins : DirectionBins G X,
      (∀ b, MeasurableSet (bins.code ⁻¹' {b}) ∧ μ (frontier (bins.code ⁻¹' {b})) = 0) ∧
      (∀ x ∈ S, ∀ y, bins.code x = bins.code y → dist x y < 1) ∧
      ∀ x ∈ S, ∀ y ∈ S, bins.code x = bins.code y → ∀ positive : Bool,
        let dir := fun z => if positive then v z else -v z
        dist (shiftTo (center x) (productLine (dir x) s))
          (shiftTo (center y) (productLine (dir y) s)) ≤ η * s := by
  let d (b : Bool) (x : X) := if b then v x else -v x
  let chart (b : Bool) (x : X) := shiftTo (center x) (productChart (s • d b x))
  let endpoint (b : Bool) (x : X) := shiftTo (center x) (productLine (d b x) s)
  have tol (b : Bool) (x : X) (hx : x ∈ S) :
      dist (chart b x) (endpoint b x) ≤ (η / 3) * s := by
    dsimp only [chart, endpoint]
    rw [(shiftTo_isometry (center x)).dist_eq]
    apply hhook
    cases b <;> simpa [d] using hunit x hx
  have cont (b : Bool) : ContinuousOn (chart b) S := by
    change ContinuousOn ((fun cv : HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) =>
      shiftTo cv.1 (productChart cv.2)) ∘ (fun z => (center z, s • d b z))) S
    apply continuous_placed_chart.continuousOn.comp (t := univ) _ (mapsTo_univ _ _)
    apply hc.prodMk
    apply (continuous_const_smul s).comp_continuousOn
    cases b <;> [exact hv.neg; exact hv]
  have scale (b : Bool) := uniformContinuousOn_iff.mp (hS.uniformContinuousOn_of_continuous (cont b))
    (η/3*s) (mul_pos (by positivity) hs)
  choose δ hδ hdiam using scale
  obtain ⟨bins, hnull, hfine⟩ := exists_directionBins (G := G) μ hS
    (lt_min (lt_min (hδ true) (hδ false)) (show (0 : ℝ) < 1 by norm_num))
  refine ⟨bins, hnull, fun x hx y he => (hfine x hx y he).trans_le (min_le_right _ _), ?_⟩
  intro x hx y hy he b
  have hxy := (hfine x hx y he).trans_le (min_le_left _ _)
  have hxy' : dist x y < δ b := by cases b <;> exact lt_of_lt_of_le hxy (by simp)
  have hcxy := hdiam b x hx y hy hxy'
  have ht := dist_triangle4 (endpoint b x) (chart b x) (chart b y) (endpoint b y)
  change dist (endpoint b x) (endpoint b y) ≤ η*s
  rw [dist_comm (endpoint b x) (chart b x)] at ht
  linarith only [ht, hcxy, tol b x hx, tol b y hy]

end Epoch

end BorderVNP
end Computability
end OAI
