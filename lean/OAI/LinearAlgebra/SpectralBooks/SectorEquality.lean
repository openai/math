import OAI.LinearAlgebra.SpectralBooks.Rigidity
import OAI.LinearAlgebra.SpectralBooks.SectorTriangleMetric

/-! # The equality case of the squared midpoint inequality -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction Set

variable {X : Type*} [MetricSpace X]

/-- The closed sector spanned by two segments of unit parameter length has
Euclidean distances, with all coefficients fixed by the distances at the vertices. -/
def EuclideanSegmentSector (g : IsGeodesic X) (a b : ℝ → X) (m x z : X) : Prop :=
  ∀ p ∈ sectorDomain (Icc 0 1), ∀ q ∈ sectorDomain (Icc 0 1),
    dist (sectorMap g a b p) (sectorMap g a b q) ^ 2 =
      (p.1-q.1)^2 * dist m x ^ 2 + (p.2-q.2)^2 * dist m z ^ 2 +
      (p.1-q.1)*(p.2-q.2)*(dist m x ^ 2 + dist m z ^ 2 - dist x z ^ 2)

/-- At equality in the squared midpoint inequality, both sectors between the
midpoint-to-endpoint segments and the segment to the third point are Euclidean.
The conclusion also covers zero-length and collinear sides. -/
theorem euclideanSegmentSectors_of_midpoint_equality (g : IsGeodesic X)
    (hB : SectorBusemann X) (hX : ScaledSectorNormRigidity X)
    {m x y z : X} (hsec : QuadraticRaySectors (CurvatureBlowup.Space m))
    {a b w : ℝ → X} (ha : IsSegment a m x) (hb : IsSegment b m y) (hw : IsSegment w m z)
    (hmx : dist m x = dist x y / 2) (hmy : dist m y = dist x y / 2)
    (hsharp : 2 * dist z m ^ 2 + dist x y ^ 2 / 2 = dist z x ^ 2 + dist z y ^ 2) :
    EuclideanSegmentSector g a w m x z ∧ EuclideanSegmentSector g b w m y z := by
  have h := (midpoint_comparison_of_quadratic_blowup hB.radial hsec ha hb hw hmx hmy).2 hsharp
  have oneSector {u : X} {r : ℝ → X} (hr : IsSegment r m u)
      (hsep : ∀ t ∈ Icc (0 : ℝ) 1, dist (r t) (w t) = t * dist u z) :
      EuclideanSegmentSector g r w m u z := by
    intro p hp q hq
    exact sectorMap_triangle_dist_sq g hB hX zero_lt_one hr.2.2 hw.2.2
      (fun t ht ↦ (hsep t ht).trans (mul_comm _ _)) hp hq
  exact ⟨oneSector ha fun t ht ↦ (h t ht).1, oneSector hb fun t ht ↦ (h t ht).2⟩

end SpectralBooks
end LinearAlgebra
end OAI
