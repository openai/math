import OAI.Computability.VPVNP.CubeFilling
import OAI.Computability.VPVNP.SpectralGeometry

/-!
# The star estimate for cube corners in a CAT(0) space

Section 4.3 of *VP and VNP differ over every field* compares the total distance
from an ambient center to the basis vertices with the wire lengths of a
balanced cut. The nearest point in the filled cube reduces the lower bound to
the Euclidean star estimate, and the cut centroids also belong to that cube.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

open scoped unitInterval symmDiff

noncomputable section

/-- The Euclidean vector with the coordinates of a point in the unit cube. -/
def cubeVector {n : ℕ} (x : Fin n → I) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i ↦ (x i : ℝ)

theorem cubeVector_corner_singleton {n : ℕ} (i : Fin n) :
    cubeVector (cubeCorner {i}) = EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases hj : j = i <;> simp [cubeVector, cubeCorner, EuclideanSpace.single, hj]

variable {X : Type*} [MetricSpace X] {n : ℕ} {scale : ℝ}

/-- The filling scales Euclidean distances by the same factor as its corners. -/
theorem fillCube_dist (h : HasCATZeroSegments X) (f : Finset (Fin n) → X)
    (hs : 0 ≤ scale) (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (x y : Fin n → I) :
    dist (fillCube h f x) (fillCube h f y) = scale * dist (cubeVector x) (cubeVector y) := by
  apply (sq_eq_sq₀ dist_nonneg (mul_nonneg hs dist_nonneg)).mp
  rw [fillCube_dist_sq h f hf, mul_pow, PiLp.dist_sq_eq_of_L2]
  simp only [cubeVector, cubeSquaredDistance, PiLp.toLp_apply, Real.dist_eq, sq_abs]

/-- The star estimate (4.4) in the ambient metric. Its center may lie anywhere
in the CAT(0) space containing the cube. -/
theorem cube_star_lower (h : HasCATZeroSegments X) (f : Finset (Fin n) → X)
    (hs : 0 ≤ scale) (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (p : X) :
    scale * starLength n ≤ ∑ i : Fin n, dist p (f {i}) := by
  obtain ⟨x, hx⟩ := fillCube_nearest h f hf p
  have hterm (i : Fin n) :
      scale * dist (EuclideanSpace.single i (1 : ℝ)) (cubeVector x) ≤ dist p (f {i}) := by
    have hi := hx (cubeCorner {i})
    rw [fillCube_dist h f hs hf, cubeVector_corner_singleton, fillCube_corner,
      dist_comm (cubeVector x)] at hi
    apply (sq_le_sq₀ (mul_nonneg hs dist_nonneg) dist_nonneg).mp
    linarith only [hi, sq_nonneg (dist p (fillCube h f x))]
  calc
    scale * starLength n = scale * ∑ i : Fin n,
        dist (EuclideanSpace.single i (1 : ℝ)) (basisCentroid n) := by
      rw [basisCentroid_star_length, starLength]
    _ ≤ scale * ∑ i : Fin n, dist (EuclideanSpace.single i (1 : ℝ)) (cubeVector x) :=
      mul_le_mul_of_nonneg_left (basisCentroid_minimizes (cubeVector x)) hs
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ ↦ hterm i

/-- Unit-cube coordinates of the centroid of the basis vertices in a side of the cut. -/
def cubeCentroidCoordinates (S : Finset (Fin n)) (i : Fin n) : I :=
  ⟨if i ∈ S then (S.card : ℝ)⁻¹ else 0, by
    by_cases hi : i ∈ S
    · have hc : 1 ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨i, hi⟩
      simp only [hi, ↓reduceIte, Set.mem_Icc]
      exact ⟨by positivity, inv_le_one_of_one_le₀ hc⟩
    · simp [hi]⟩

private theorem cubeVector_centroid (S : Finset (Fin n)) :
    cubeVector (cubeCentroidCoordinates S) = subsetCentroid S := rfl

/-- The side centroid realized in the CAT(0) target by filling the marked cube. -/
def filledSubsetCentroid (h : HasCATZeroSegments X)
    (f : Finset (Fin n) → X) (S : Finset (Fin n)) : X :=
  fillCube h f (cubeCentroidCoordinates S)

/-- The distance from an individual basis terminal to a side centroid. -/
theorem basis_dist_filledSubsetCentroid (h : HasCATZeroSegments X)
    (f : Finset (Fin n) → X) (hs : 0 ≤ scale)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (S : Finset (Fin n)) (i : Fin n) :
    dist (f {i}) (filledSubsetCentroid h f S) =
      scale * dist (EuclideanSpace.single i (1 : ℝ)) (subsetCentroid S) := by
  rw [← fillCube_corner h f {i}, filledSubsetCentroid, fillCube_dist h f hs hf,
    cubeVector_corner_singleton, cubeVector_centroid]

/-- Total distance of one side's terminal wires in a scaled CAT(0) cube. -/
theorem filledSubsetCentroid_star_length (h : HasCATZeroSegments X)
    (f : Finset (Fin n) → X) (hs : 0 ≤ scale)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (S : Finset (Fin n)) :
    ∑ i ∈ S, dist (f {i}) (filledSubsetCentroid h f S) =
      scale * √((S.card : ℝ) * ((S.card : ℝ) - 1)) := by
  simp only [basis_dist_filledSubsetCentroid h f hs hf, ← Finset.mul_sum,
    subsetCentroid_star_length]

/-- Distance between the centroids of disjoint sides of a scaled CAT(0) cube. -/
theorem disjoint_filledSubsetCentroids_dist (h : HasCATZeroSegments X)
    (f : Finset (Fin n) → X) (hs : 0 ≤ scale)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    {S T : Finset (Fin n)} (hST : Disjoint S T) :
    dist (filledSubsetCentroid h f S) (filledSubsetCentroid h f T) =
      scale * √((S.card : ℝ)⁻¹ + (T.card : ℝ)⁻¹) := by
  rw [filledSubsetCentroid, filledSubsetCentroid, fillCube_dist h f hs hf,
    cubeVector_centroid, cubeVector_centroid, disjoint_subsetCentroids_dist hST]

/-- In a positively scaled cube of dimension at least `18 * C²`, a balanced
two-centroid layout costs strictly less than a star with any ambient center. -/
theorem filled_balancedLayout_strict (h : HasCATZeroSegments X) {C : ℝ}
    (f : Finset (Fin n) → X) (hs : 0 < scale)
    (hf : ∀ A B, dist (f A) (f B) ^ 2 = scale ^ 2 * (A ∆ B).card)
    (hC : 1 ≤ C) (hdim : 18 * C ^ 2 ≤ n)
    (S : Finset (Fin n)) (hlo : n ≤ 3 * S.card) (hhi : 3 * S.card ≤ 2 * n) (p : X) :
    (∑ i ∈ S, dist (f {i}) (filledSubsetCentroid h f S)) +
      (∑ i ∈ Sᶜ, dist (f {i}) (filledSubsetCentroid h f Sᶜ)) +
      C * dist (filledSubsetCentroid h f S) (filledSubsetCentroid h f Sᶜ) <
      ∑ i : Fin n, dist p (f {i}) := by
  have he := balancedLayout_strict hC hdim S hlo hhi (basisCentroid n)
  rw [subsetCentroid_star_length, subsetCentroid_star_length,
    disjoint_subsetCentroids_dist disjoint_compl_right, basisCentroid_star_length] at he
  apply lt_of_lt_of_le _ (cube_star_lower h f hs.le hf p)
  rw [filledSubsetCentroid_star_length h f hs.le hf,
    filledSubsetCentroid_star_length h f hs.le hf,
    disjoint_filledSubsetCentroids_dist h f hs.le hf disjoint_compl_right]
  rw [mul_left_comm C scale, ← mul_add, ← mul_add]
  exact mul_lt_mul_of_pos_left he hs

end

end SpectralGeometry

end VPVNP
end Computability
end OAI
