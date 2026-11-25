import OAI.LinearAlgebra.SpectralBooks.PriceBlowup
import OAI.LinearAlgebra.SpectralBooks.TangentFlat

/-!
# Spectral axis rigidity in a CAT(0) extension

Restricting placement prices to an isometrically embedded space preserves each
of the spectral price laws. Thus the tangent flat furnished by the marked-site
inequality is a spectral Euclidean flat over the same field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SiteTensor HyperbolicObstruction Crossing

namespace SpectralPlacementPrices

variable {K X : Type*} [Field K]

/-- A marked placement with positive diagonal price cannot consist of
copies of one point. -/
theorem exists_dist_pos_of_diagonal_pos [MetricSpace X] (P : SpectralPlacementPrices K X)
    {I : Type} [Fintype I] [Nonempty I] (y : I → X)
    (hpos : 0 < P.price (Raw.diagonal I K (Fin 2)) y) : ∃ p q, 0 < dist (y p) (y q) := by
  classical
  by_contra! hzero
  let c : I := Classical.choice inferInstance
  have hc : y = fun _ => y c := funext fun i => dist_eq_zero.mp ((hzero i c).antisymm dist_nonneg)
  rw [hc, P.collapsed] at hpos
  exact hpos.false

end SpectralPlacementPrices

/-- The conclusion of Lemma `axis-rigidity` after extending the finite
spectral placement into a CAT(0) spectral space. Its crossing price is the
sum of the prices of the binary diameter wires. -/
theorem spectral_flat_of_diameter_average {K X : Type*} [Field K] [MetricSpace X]
    (P : SpectralPlacementPrices K X) (h : CATZero X) {D : ℕ} (hD : 0 < D)
    (y : AxisSite D → X) (hdiag : 0 < P.price (Raw.diagonal _ K (Fin 2)) y)
    (hcontract : ∀ p q, dist (y p) (y q) ≤
      diameterSum y / (2 * D) * dist (axisPoint p) (axisPoint q)) :
    Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D))) := by
  obtain ⟨f, hf⟩ := exists_tangent_flat_of_diameter_average h hD y
    (P.exists_dist_pos_of_diagonal_pos y hdiag) hcontract
  exact ⟨(P.tangentCone h (y none)).pullback f hf⟩

/-- A missing spectral flat forces a strict excess in price per Euclidean
length on some unordered pair, even if the winning pair depends on the
initial spectral placement. -/
theorem exists_pair_of_no_spectral_flat {K X : Type*} [Field K] [MetricSpace X]
    (P : SpectralPlacementPrices K X) (h : CATZero X) {D : ℕ} (hD : 0 < D)
    (y : AxisSite D → X) (hdiag : 0 < P.price (Raw.diagonal _ K (Fin 2)) y)
    (hmissing : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D)))) :
    ∃ e : AxisPair D, diameterSum y < (2 * D / axisLength e) *
      dist (y e.val.out.1) (y e.val.out.2) := by
  apply exists_pair_of_no_tangent_flat h hD y (P.exists_dist_pos_of_diagonal_pos y hdiag)
  rintro ⟨f, hf⟩
  exact hmissing ⟨(P.tangentCone h (y none)).pullback f hf⟩

end SpectralBooks
end LinearAlgebra
end OAI
