import OAI.Hierarchy.FlatPrices

namespace OAI
/-! # Convexity on lines and finite transport costs for placed tensors -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks
open scoped BigOperators

variable {F E : Type*} [Field F] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : SpectralPlacementPrices F E) {I : Type} [Fintype I] (T : SiteTensor.Raw.{0} I F)

/-- Joint convexity restricts to every affine line in the space of placements. -/
theorem convex_price_line (x y : I → E) :
    ConvexOn ℝ Set.univ (fun t : ℝ => P.price T (t • y + x)) := by
  have h := (P.convexOn_price T).comp_affineMap (AffineMap.lineMap x (y+x))
  simpa only [Set.preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
    add_sub_cancel_right] using h

omit [NormedSpace ℝ E] in
/-- Bringing every leg to one site bounds a price, even for the empty list of sites. -/
theorem price_le_transport (x : I → E) (c : E) :
    P.price T x ≤ ∑ i, dist (x i) c * Real.logb 2 (Fintype.card (T.Leg i)) := by
  have h := P.transport T x (fun _ => c)
  rw [P.collapsed, Real.dist_eq, sub_zero] at h
  exact (le_abs_self _).trans h

/-- Scaling every leg scales the upper bound from transporting to the origin. -/
theorem price_ray_bound (x : I → E) (t : ℝ) (ht : 0 < t) :
    P.price T (t • x) ≤ t * ∑ i, ‖x i‖ * Real.logb 2 (Fintype.card (T.Leg i)) := by
  simpa only [Pi.smul_apply, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le,
    Finset.mul_sum, mul_assoc] using price_le_transport P T (t • x) 0

omit [NormedSpace ℝ E] in
/-- A common translation has the same cost bound for every displacement. -/
theorem price_translate_bound (x : I → E) (c : E) :
    P.price T (fun i => x i + c) ≤ ∑ i, ‖x i‖ * Real.logb 2 (Fintype.card (T.Leg i)) := by
  simpa only [dist_eq_norm, add_sub_cancel_right] using
    price_le_transport P T (fun i => x i + c) c

end Hierarchy

end OAI
