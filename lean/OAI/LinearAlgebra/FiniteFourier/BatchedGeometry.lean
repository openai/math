import OAI.LinearAlgebra.FiniteFourier.BatchedDetection
import OAI.LinearAlgebra.FiniteFourier.BatchedScales

/-! # The common triangle and rectangle placements for the batch -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical
noncomputable section

def batchCenter : Plane := WithLp.toLp 2 ![0,0]
def batchHub : Plane := WithLp.toLp 2 ![-1/4,0]

private theorem batch_plane_dist (a b c d : ℝ) :
    dist (WithLp.toLp 2 ![a,b] : Plane) (WithLp.toLp 2 ![c,d]) =
      Real.sqrt ((a-c)^2 + (b-d)^2) := by
  simp [PiLp.dist_eq_of_L2, Fin.sum_univ_two, Real.dist_eq]

theorem batch_vertical {L : ℝ} (hL : 0 ≤ L) :
    dist (rectangleSites L 1 0) (rectangleSites L 1 2) = L ∧
    dist (rectangleSites L 1 1) (rectangleSites L 1 3) = L := by
  constructor <;> simp [rectangleSites, batch_plane_dist, show L/2 - -L/2 = L by ring, Real.sqrt_sq hL]

theorem batch_center_dist (L : ℝ) (i : Fin 4) :
    dist batchCenter (rectangleSites L 1 i) = Real.sqrt (L^2 + 1) / 2 := by
  have he : Real.sqrt ((L^2 + 1)/4) = Real.sqrt (L^2 + 1) / 2 := by
    rw [Real.sqrt_div (by positivity)]
    norm_num
  rw [← he]
  fin_cases i
  · exact (batch_plane_dist 0 0 (-1/2) (L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (batch_plane_dist 0 0 (1/2) (L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (batch_plane_dist 0 0 (-1/2) (-L/2)).trans (congrArg Real.sqrt (by ring))
  · exact (batch_plane_dist 0 0 (1/2) (-L/2)).trans (congrArg Real.sqrt (by ring))

theorem batch_hub_dist : dist batchCenter batchHub = 1/4 := by
  rw [batchCenter, batchHub, batch_plane_dist]
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
  norm_num

theorem batch_hub_semiperimeter {L : ℝ} (hL : 0 ≤ L) :
    (dist batchHub (rectangleSites L 1 0) + dist batchHub (rectangleSites L 1 2) +
      dist (rectangleSites L 1 0) (rectangleSites L 1 2)) / 2 = batchHubTriangle L := by
  rw [(batch_vertical hL).1]
  have he (y : ℝ) (hy : y^2 = L^2/4) :
      dist batchHub (WithLp.toLp 2 ![-1/2,y]) = Real.sqrt (1/16 + L^2/4) := by
    rw [batchHub, batch_plane_dist]
    exact congrArg Real.sqrt (by nlinarith)
  change (dist batchHub (WithLp.toLp 2 ![-1/2,L/2]) +
    dist batchHub (WithLp.toLp 2 ![-1/2,-L/2]) + L) / 2 = _
  rw [he _ (by ring), he _ (by ring), batchHubTriangle]
  ring

variable {K : Type*} [Field K] (P : SpectralPlacementPrices K Plane)

theorem exists_batch_triangle_points
    (hflat : ∀ (s : Finset Plane) (hs : s.Nonempty), P.diagonal s = meanWidth s hs)
    {L : ℝ} (hL : 0 < L) :
    ∃ φ χ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 3) K → _ → Prop),
      PricesListsAt P φ batchCenter (rectangleSites L 1 0) (rectangleSites L 1 2) (batchTriangle L) ∧
      PricesListsAt P χ batchCenter (rectangleSites L 1 1) (rectangleSites L 1 3) (batchTriangle L) := by
  obtain ⟨hl, hr⟩ := batch_vertical hL.le
  obtain ⟨φ, hφ⟩ := exists_list_triangle_point P hflat batchCenter _ _ (hl.symm ▸ hL)
  obtain ⟨χ, hχ⟩ := exists_list_triangle_point P hflat batchCenter _ _ (hr.symm ▸ hL)
  rw [batch_center_dist, batch_center_dist, hl] at hφ
  rw [batch_center_dist, batch_center_dist, hr] at hχ
  have he : (Real.sqrt (L^2+1)/2 + Real.sqrt (L^2+1)/2 + L)/2 = batchTriangle L := by
    unfold batchTriangle
    ring
  rw [he] at hφ hχ
  exact ⟨φ, χ, hφ, hχ⟩

theorem exists_batch_rectangle_point {L : ℝ} (hL : 0 < L)
    (hnorm : P.price (Raw.diagonal (Fin 4) K (Fin 2)) (rectangleSites L 1) = L+1) :
    ∃ ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin 4) K → _ → Prop),
      ∀ (I : Type) [Fintype I] (M : Matrix I I K),
      fourierPhasePrice P M (rectangleSites L 1) = (L+1) * Real.logb 2 (phasePointValue ψ M) := by
  rcases placed_price_normalized_or_collapsed P (rectangleSites L 1) with hc | ⟨ψ, t, _, he⟩
  · rw [hc] at hnorm
    linarith
  have ht : t = L+1 := by
    rw [he, rawLogPrice, ofRaw_diagonal_eq_natCast,
      show ψ.val (Fintype.card (Fin 2) : TensorClass (Fin 4) K) = Fintype.card (Fin 2) from
        map_natCast (normalizedSpectrum.toRingHom ψ) _] at hnorm
    simpa using hnorm
  subst t
  exact ⟨ψ, fun _ _ M => he (phaseRaw M)⟩

end
end FiniteFourier
end LinearAlgebra
end OAI
