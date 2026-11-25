import OAI.Geometry.HyperbolicGroups.ConeData

/-!
# Orthogonal axes in the tangent cone

The logarithms of endpoints of unit diameters through a common center give
opposite pairs in the tangent cone. If distinct diameters have all four endpoint
distances at most `√2`, their cone pairings vanish.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction

/-- The four cross-distance bounds between each two diameters yield orthogonal
axes of the prescribed radius based at the common midpoint. -/
theorem axisLogs_orthogonal_of_radius {X : Type*} [MetricSpace X] {D : ℕ}
    (h : CATZero X) (o : X) (x : Fin D → Bool → X)
    {r : ℝ} (hr : 0 ≤ r) (hrad : ∀ i a, dist o (x i a) = r)
    (hdiam : ∀ i, dist (x i false) (x i true) = 2 * r)
    (hcross : ∀ i j, i ≠ j → ∀ a b, dist (x i a) (x j b) ≤ r * Real.sqrt 2) :
    (∀ i a, (TangentCone.coneData h o).normSq (TangentCone.log h o (x i a)) = r ^ 2) ∧
    (∀ i, (TangentCone.coneData h o).Opposite
      (TangentCone.log h o (x i false)) (TangentCone.log h o (x i true))) ∧
    (∀ i j, i ≠ j → ∀ a b, (TangentCone.coneData h o).pairing
      (TangentCone.log h o (x i a)) (TangentCone.log h o (x j b)) = 0) := by
  have hop (i) : (TangentCone.coneData h o).Opposite
      (TangentCone.log h o (x i false)) (TangentCone.log h o (x i true)) := by
    have hm : o = CATZero.mid h (x i false) (x i true) := by
      apply CATZero.eq_segment_of_dist h (by norm_num : 1 / 2 ∈ Set.Icc (0 : ℝ) 1)
      · rw [dist_comm, hrad, hdiam]
        ring
      · rw [hrad, hdiam]
        ring
    rw [hm]
    exact TangentCone.opposite_mid_logs h _ _
  refine ⟨fun i a => by rw [TangentCone.normSq_log, hrad], hop, ?_⟩
  intro i j hij a b
  have hnonneg (s : Bool) : 0 ≤ (TangentCone.coneData h o).pairing
      (TangentCone.log h o (x i s)) (TangentCone.log h o (x j b)) := by
    have hp := TangentCone.pairing_log_ge h o (x i s) (x j b)
    rw [hrad, hrad] at hp
    have hd := (sq_le_sq₀ dist_nonneg (mul_nonneg hr (Real.sqrt_nonneg 2))).2 (hcross i j hij s b)
    rw [mul_pow, Real.sq_sqrt (by norm_num)] at hd
    linarith
  have hsum := (TangentCone.coneData h o).opposite_pairing (TangentCone.catZero h o)
    (hop i) (TangentCone.log h o (x j b))
  cases a <;> linarith [hnonneg false, hnonneg true]

/-- Unit-normalized endpoint data give orthogonal unit logarithms. -/
theorem axisLogs_orthogonal {X : Type*} [MetricSpace X] {D : ℕ}
    (h : CATZero X) (o : X) (x : Fin D → Bool → X)
    (hrad : ∀ i a, dist o (x i a) = 1)
    (hdiam : ∀ i, dist (x i false) (x i true) = 2)
    (hcross : ∀ i j, i ≠ j → ∀ a b, dist (x i a) (x j b) ≤ Real.sqrt 2) :
    (∀ i a, (TangentCone.coneData h o).normSq (TangentCone.log h o (x i a)) = 1) ∧
    (∀ i, (TangentCone.coneData h o).Opposite
      (TangentCone.log h o (x i false)) (TangentCone.log h o (x i true))) ∧
    (∀ i j, i ≠ j → ∀ a b, (TangentCone.coneData h o).pairing
      (TangentCone.log h o (x i a)) (TangentCone.log h o (x j b)) = 0) := by
  simpa using axisLogs_orthogonal_of_radius h o x zero_le_one hrad
    (by simpa using hdiam) (by simpa using hcross)

end SpectralBooks
end LinearAlgebra
end OAI
