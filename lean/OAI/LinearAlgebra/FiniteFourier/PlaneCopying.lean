import OAI.LinearAlgebra.FiniteFourier.Geometry
import OAI.LinearAlgebra.SpectralBooks.PlacedLabelCopy
import OAI.LinearAlgebra.SpectralBooks.TriangleSemiperimeter

/-! # Copying a common basis label in the spectral plane

A label present on two legs can be appended at a third site at a cost bounded
by half the extra path length times the logarithm of its dimension.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

variable {K : Type*} [Field K]

/-- The common-label copying law of Theorem `geo:spectrum`, on arbitrary finite lists
of sites, including repeated positions. -/
def PlaneCopying (P : SpectralPlacementPrices K Plane) : Prop :=
  ∀ {I : Type} [Fintype I] [Nonempty I] (T : Raw.{0} I K) (x : I → Plane) (σ : Fin 3 → I)
    {q : ℕ} (_hq : 0 < q) (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q),
    (∀ z, T.coeff z ≠ 0 → hA (z (σ 0)) = hB (z (σ 1))) →
    P.price (T.appendLabel (σ 2) (Fin q) (fun z ↦ hA (z (σ 0)))) x ≤ P.price T x +
      ((dist (x (σ 0)) (x (σ 2)) + dist (x (σ 1)) (x (σ 2)) - dist (x (σ 0)) (x (σ 1))) / 2) *
        Real.logb 2 q

/-- If the receiving site is the center of two opposite points, copying the
common label there has zero extra price. -/
theorem PlaneCopying.copy_midpoint {P : SpectralPlacementPrices K Plane} (hc : PlaneCopying P)
    {I : Type} [Fintype I] [Nonempty I] (T : Raw.{0} I K) (x : I → Plane) (σ : Fin 3 → I)
    {q : ℕ} (hq : 0 < q) (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hmatch : ∀ z, T.coeff z ≠ 0 → hA (z (σ 0)) = hB (z (σ 1)))
    (hopp : x (σ 1) = -x (σ 0)) (horig : x (σ 2) = 0) :
    P.price (T.appendLabel (σ 2) (Fin q) (fun z ↦ hA (z (σ 0)))) x ≤ P.price T x := by
  have h := hc T x σ hq hA hB hmatch
  have hd (v : Plane) : dist v (-v) = 2 * ‖v‖ := by
    rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ v, norm_smul]
    norm_num
  simpa only [hopp, horig, dist_zero_right, norm_neg, hd, ← two_mul, sub_self, zero_div,
    zero_mul, add_zero] using h

noncomputable local instance planeCopyingDecidableEq : DecidableEq Plane := Classical.decEq _
private theorem diagonal_price_three_le (P : SpectralPlacementPrices K Plane) (y : Fin 3 → Plane) :
    P.price (Raw.diagonal (Fin 3) K (Fin 2)) y ≤ (dist (y 0) (y 1) + dist (y 1) (y 2) +
      dist (y 0) (y 2)) / 2 := by
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  rw [P.price_binaryDiagonal_eq, hu, Finset.image_insert, Finset.image_insert, Finset.image_singleton,
    dist_comm (y 0) (y 2)]
  exact P.diagonal_triangle_le_half_perimeter _ _ _


/-- The copying degeneration and the triangle semiperimeter upper bound
give formula (geo:copy) over every field and at every placement. -/
theorem planeCopying_of_spectralPrices (P : SpectralPlacementPrices K Plane) : PlaneCopying P := by
  intro I _ _ T x σ q hq hA hB hm
  apply (P.copyLabel_price_le T x σ hq hA hB hm).trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (Real.logb_nonneg (by norm_num) (by exact_mod_cast hq))
  have h := diagonal_price_three_le P (x ∘ σ)
  simp only [Function.comp_apply] at h
  linarith

end FiniteFourier
end LinearAlgebra
end OAI
