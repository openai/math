import OAI.LinearAlgebra.SpectralBooks.SpectralMetricLimit
import OAI.ThreeFlat.CrossingEscape
import OAI.ThreeFlat.Scale
import OAI.ThreeFlat.EscapingLines
import OAI.HyperbolicObstruction.ParallelSpace
import OAI.ThreeFlat.ProductFlat

namespace OAI
/-! # The six-terminal catalytic crossing comparison

Four sites with total pair distance one cannot violate the transverse matching
bound by a fixed positive amount while their excess over a long common path
tends to zero. The limiting parallel set splits off a line, and a four-point
defect in the transverse factor produces a spectral three-flat.
-/

open Filter HyperbolicObstruction HyperbolicObstruction.MetricLimit
open scoped BigOperators Topology

namespace ThreeFlat

open LinearAlgebra.SpectralBooks

/-- A configuration of two catalyst endpoints and four crossing terminals in
a spectral CAT(0) space. -/
structure CrossingPlacement (F : Type*) [Field F] where
  carrier : Type
  [metric : MetricSpace carrier]
  prices : SpectralPlacementPrices F carrier
  cat : CATZero carrier
  A : carrier
  B : carrier
  x : Fin 4 → carrier

attribute [instance] CrossingPlacement.metric

namespace CrossingPlacement

variable {F : Type*} [Field F] (p : CrossingPlacement F)

def d (i j : Fin 4) : ℝ := dist (p.x i) (p.x j)

def phase (i : Fin 4) : ℝ := dist p.A (p.x i) - dist p.B (p.x i)

def excess (i : Fin 4) : ℝ := dist p.A (p.x i) + dist p.B (p.x i) - dist p.A p.B

theorem excess_nonneg (i : Fin 4) : 0 ≤ p.excess i := by
  unfold excess
  linarith [dist_triangle_right p.A p.B (p.x i)]

end CrossingPlacement

private theorem cost_le_from_parallel_product
    {F X : Type*} [Field F] [MetricSpace X] (P : SpectralPlacementPrices F X) (hX : CATZero X)
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    {b : X → ℝ} (hb : LipschitzWith 1 b) (l : Fin 4 → ℝ → X) (c : Fin 4 → ℝ)
    (hl : ∀ i, Isometry (l i)) (hc : ∀ i t, b (l i t) = c i + t)
    (hp : ∀ i, ∃ C : ℝ, ∀ t, dist (l i t) (l 0 t) ≤ C) :
    let d := fun i j => dist (l i 0) (l j 0)
    xDemand d ≤ xSide d + phaseCorr (fun i => 2 * c i) := by
  obtain ⟨Y, met, hY, e, y, he, hy⟩ :=
    CATZero.exists_parallel_product hX hb l c (l 0) hl hc hp
  let q := fun i j => dist (y i) (y j)
  have htree : xDemand q ≤ xSide q := by
    apply le_of_not_gt
    intro hbad
    apply hno
    apply spectralThreeFlat_of_transverse_fourPointDefect P hX hY e he
      (y 0) (y 2) (y 1) (y 3)
    simpa only [xSide, xDemand, q, dist_comm (y 2) (y 1)] using hbad
  have hd (i j : Fin 4) : dist (l i 0) (l j 0) ^ 2 =
      |c i - c j| ^ 2 + q i j ^ 2 := by
    rw [hy, hy, he, Real.sq_sqrt (by positivity), Real.dist_eq]
  apply crossing_le_of_transverse_fourPoint c htree
  · intro i j
    have hn : 0 ≤ q i j := dist_nonneg
    apply (sq_le_sq₀ hn dist_nonneg).mp
    rw [hd]
    linarith [sq_nonneg |c i - c j|]
  · intro i j
    have hn : 0 ≤ q i j := dist_nonneg
    apply (sq_le_sq₀ dist_nonneg (add_nonneg hn (abs_nonneg _))).mp
    rw [hd]
    nlinarith [mul_nonneg hn (abs_nonneg (c i - c j))]

/-- At total terminal distance one, absence of a spectral three-flat gives a
single path-excess coefficient for all spectral CAT(0) placements. -/
theorem exists_normalized_catalytic_crossing {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ p : CrossingPlacement F, xMass p.d = 1 →
      xDemand p.d ≤ xSide p.d + τ + phaseCorr p.phase +
        ((n : ℝ) + 1) * ∑ i, p.excess i := by
  classical
  by_contra! h
  choose p hnorm hbad using h
  let X := fun n => (p n).carrier
  let o := fun n => (p n).x 0
  let A := fun n => (p n).A
  let B := fun n => (p n).B
  let g := fun n => (p n).cat
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  let x (i : Fin 4) : Bounded U X o := ⟨fun n => (p n).x i, 1, fun n =>
    (le_xMass (d := (p n).d) (fun _ _ => dist_nonneg) 0 i).trans_eq (hnorm n)⟩
  obtain ⟨hsmall, ha, hb⟩ :=
    crossing_escape g A B (fun n => (p n).x) hτ hnorm hbad
  have hA := ha.mono_left hU
  have hB := hb.mono_left hU
  have hε (i : Fin 4) := (hsmall i).mono_left hU
  let l (i : Fin 4) := escapingLine g A B (x i)
  let c (i : Fin 4) := endpointPotential U A (point (x i))
  let d (i j : Fin 4) := dist (point (x i)) (point (x j))
  have hc := cost_le_from_parallel_product
    (SpectralPlacementPrices.metricLimit U (fun n => (p n).prices)) (MetricLimit.catZero g)
    hno (lipschitzWith_endpointPotential U (o := o) A) l c
    (fun i => escapingLine_isometry g A B (x i) hA hB (hε i))
    (fun i t => (endpointPotential_escapingLine g A B (x i) hA hB (hε i) t).1)
    (fun i => ⟨d i 0, escapingLine_dist_le g A B (x i) (x 0) hA hB⟩)
  change xDemand (fun i j => dist (escapingLine g A B (x i) 0) (escapingLine g A B (x j) 0))
      ≤ xSide (fun i j => dist (escapingLine g A B (x i) 0) (escapingLine g A B (x j) 0))
      + phaseCorr (fun i => 2 * c i) at hc
  simp only [escapingLine_zero] at hc
  have hd (i j : Fin 4) : Tendsto (fun n => (p n).d i j) U (𝓝 (d i j)) :=
    tendsto_point_dist (x i) (x j)
  have hdem : Tendsto (fun n => xDemand (p n).d) U (𝓝 (xDemand d)) :=
    (hd 0 2).add (hd 1 3)
  have hside : Tendsto (fun n => xSide (p n).d) U (𝓝 (xSide d)) :=
    ((hd 0 1).add (hd 2 3)).max ((hd 0 3).add (hd 1 2))
  have hphase (i j : Fin 4) :
      Tendsto (fun n => |(p n).phase i - (p n).phase j|) U
        (𝓝 (|2 * c i - 2 * c j|)) := by
    rw [← mul_sub]
    exact (tendsto_endpoint_phase_difference U A B (x i) (x j) (hε i) (hε j)).abs
  have hcorr : Tendsto (fun n => phaseCorr (p n).phase) U (𝓝 (phaseCorr (fun i => 2 * c i))) :=
    ((hphase 0 2).add (hphase 1 3)).div_const 2
  have hlimit : xSide d + τ + phaseCorr (fun i => 2 * c i) ≤ xDemand d :=
    le_of_tendsto_of_tendsto' ((hside.add_const τ).add hcorr) hdem (fun n =>
      (le_add_of_nonneg_right (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => (p n).excess_nonneg i))).trans (hbad n).le)
  change xDemand d ≤ xSide d + phaseCorr (fun i => 2 * c i) at hc
  linarith

namespace CrossingPlacement

variable {F : Type*} [Field F]

/-- Rescaling all six distances uses a constant family in the spectral blowup. -/
noncomputable def scale (p : CrossingPlacement F) (r : ℝ) (hr : 0 < r) :
    CrossingPlacement F where
  carrier := MetricScale.Space r hr p.carrier
  prices := scaledSpectralPrices p.prices p.A r hr
  cat := MetricScale.catZero p.cat
  A := ⟨p.A⟩
  B := ⟨p.B⟩
  x := fun i => ⟨p.x i⟩

theorem scale_phase (p : CrossingPlacement F) {r : ℝ} (hr : 0 < r) (i : Fin 4) :
    (p.scale r hr).phase i = r * p.phase i := by
  change r * dist p.A (p.x i) - r * dist p.B (p.x i) = r * (dist p.A (p.x i) - dist p.B (p.x i))
  ring

theorem scale_excess (p : CrossingPlacement F) {r : ℝ} (hr : 0 < r) (i : Fin 4) :
    (p.scale r hr).excess i = r * p.excess i := by
  change r * dist p.A (p.x i) + r * dist p.B (p.x i) - r * dist p.A p.B =
    r * (dist p.A (p.x i) + dist p.B (p.x i) - dist p.A p.B)
  ring

end CrossingPlacement

/-- The scalar catalytic crossing estimate of the six-terminal construction,
uniform over the complete spectral realizations of all finite normalized points. -/
theorem exists_catalytic_crossing_price {F : Type*} [Field F]
    (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ R : ℕ, 4 ≤ R ∧ ∀ p : CrossingPlacement F,
      xDemand p.d ≤ xSide p.d + τ * xMass p.d + phaseCorr p.phase +
        ((R : ℝ) / 4) * ∑ i, p.excess i := by
  obtain ⟨n, hn⟩ := exists_normalized_catalytic_crossing hno hτ
  refine ⟨4*(n+1), by omega, ?_⟩
  intro p
  have hR : ((4 * (n + 1) : ℕ) : ℝ) / 4 = n + 1 := by push_cast; ring
  rw [hR]
  have hm : 0 ≤ xMass p.d := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  rcases hm.eq_or_lt with hz | hpos
  · have he (i j : Fin 4) : p.d i j = 0 :=
      le_antisymm ((le_xMass (d := p.d) (fun _ _ => dist_nonneg) i j).trans_eq hz.symm) dist_nonneg
    simp only [xDemand, xSide, he, zero_add, max_self, ← hz, mul_zero]
    unfold phaseCorr
    have hs : 0 ≤ ∑ i, p.excess i := Finset.sum_nonneg fun i _ => p.excess_nonneg i
    positivity
  · let r := (xMass p.d)⁻¹
    have hr : 0 < r := inv_pos.mpr hpos
    have h1 : r * xMass p.d = 1 := inv_mul_cancel₀ hpos.ne'
    let q := p.scale r hr
    have hd : q.d = fun i j => r * p.d i j := rfl
    have hnorm : xMass q.d = 1 := by rw [hd, xMass_mul, h1]
    have h := hn q hnorm
    rw [hd, xDemand_mul, xSide_mul hr.le,
      (show q.phase = fun i => r * p.phase i from funext (p.scale_phase hr)),
      phaseCorr_mul hr.le] at h
    simp_rw [show ∀ i, q.excess i = r * p.excess i from p.scale_excess hr] at h
    rw [← Finset.mul_sum] at h
    refine (mul_le_mul_iff_right₀ hr).mp ?_
    calc
      r * xDemand p.d ≤ _ := h
      _ = r * (xSide p.d + τ * xMass p.d + phaseCorr p.phase +
          ((n : ℝ) + 1) * ∑ i, p.excess i) := by
        calc
          _ = r * xSide p.d + τ * (r * xMass p.d) + r * phaseCorr p.phase +
              ((n : ℝ)+1) * (r * ∑ i, p.excess i) := by rw [h1, mul_one]
          _ = _ := by ring

end ThreeFlat

end OAI
