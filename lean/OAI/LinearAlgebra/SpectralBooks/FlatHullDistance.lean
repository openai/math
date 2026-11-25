import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Determining distances above a Euclidean hyperplane

If distances to every point of a flat agree with those in a Euclidean
half-space, the triangle inequality gives the Euclidean lower bound between
any two points on its upper side. This gives the lower metric estimate for
the filled hull of the flat and the tangent point in the book construction.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace X]

private theorem norm_sub_extension (u v : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖u - (v + t • (v - u))‖ = (1 + t) * ‖u - v‖ ∧
    ‖v - (v + t • (v - u))‖ = t * ‖u - v‖ := by
  rw [show u - (v + t • (v - u)) = (1 + t) • (u - v) by module,
    show v - (v + t • (v - u)) = t • (u - v) by module]
  simp [norm_smul, abs_of_nonneg ht, abs_of_nonneg (show 0 ≤ 1 + t by linarith)]

private theorem sqrt_sq_dilate (c d h : ℝ) (hc : 0 ≤ c) :
    Real.sqrt ((c * d) ^ 2 + (c * h) ^ 2) = c * Real.sqrt (d ^ 2 + h ^ 2) := by
  rw [show (c * d) ^ 2 + (c * h) ^ 2 = c ^ 2 * (d ^ 2 + h ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]

private theorem upper_flat_dist_le_of_lt (flat : E → X) {x y : X} {u v : E}
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a)
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + b ^ 2)) :
    Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) ≤ dist x y := by
  let t := b / (a - b)
  have ht : 0 ≤ t := div_nonneg hb (sub_nonneg.mpr hba.le)
  have ht₀ : t * (a - b) = b := div_mul_cancel₀ _ (sub_ne_zero.mpr hba.ne')
  have ht₁ : (1 + t) * (a - b) = a := by linarith [add_mul 1 t (a - b)]
  let w := v + t • (v - u)
  obtain ⟨hu, hv⟩ := norm_sub_extension u v ht
  have h := dist_triangle x y (flat w)
  rw [hx, hy, hu, hv] at h
  have hx' : Real.sqrt (((1 + t) * ‖u - v‖) ^ 2 + a ^ 2) =
      (1 + t) * Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) := by
    conv_lhs => rw [← ht₁]
    exact sqrt_sq_dilate _ _ _ (by linarith)
  have hy' : Real.sqrt ((t * ‖u - v‖) ^ 2 + b ^ 2) =
      t * Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) := by
    conv_lhs => rw [← ht₀]
    exact sqrt_sq_dilate _ _ _ ht
  rw [hx', hy'] at h
  linarith

private theorem upper_flat_dist_le_of_eq (flat : E → X) {x y : X} {u v : E} {a : ℝ}
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + a ^ 2)) :
    ‖u - v‖ ≤ dist x y := by
  by_contra! h
  let d := ‖u - v‖
  let ε := d - dist x y
  have hε : 0 < ε := sub_pos.mpr h
  have hd : 0 < d := lt_of_le_of_lt dist_nonneg h
  let t := a ^ 2 / (d * ε)
  have ht : 0 ≤ t := div_nonneg (sq_nonneg _) (mul_pos hd hε).le
  have ht' : t * (d * ε) = a ^ 2 := div_mul_cancel₀ _ (mul_pos hd hε).ne'
  let w := v + t • (v - u)
  have htri := dist_triangle x y (flat w)
  obtain ⟨hu, hv⟩ := norm_sub_extension u v ht
  rw [hx, hy, hu, hv] at htri
  have hlow : (1 + t) * d ≤ Real.sqrt (((1 + t) * d) ^ 2 + a ^ 2) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    linarith [sq_nonneg a]
  have hhigh : t * d + ε ≤ Real.sqrt ((t * d) ^ 2 + a ^ 2) := by
    change _ ≤ dist x y + Real.sqrt ((t * d) ^ 2 + a ^ 2) at htri
    dsimp only [ε]
    linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ t * d + ε) (Real.sqrt_nonneg _)).mpr hhigh
  rw [Real.sq_sqrt (by positivity)] at hsq
  nlinarith [sq_pos_of_pos hε, sq_nonneg a]

/-- Two points on the same side of a Euclidean flat, whose distances to that
flat are known, are separated by at least the Euclidean distance between
their model positions. For different heights the joining line meets the
flat, and for equal heights one tests points arbitrarily far along the flat. -/
theorem euclidean_halfSpace_dist_le (flat : E → X) {x y : X} {u v : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ w, dist x (flat w) = Real.sqrt (‖u - w‖ ^ 2 + a ^ 2))
    (hy : ∀ w, dist y (flat w) = Real.sqrt (‖v - w‖ ^ 2 + b ^ 2)) :
    Real.sqrt (‖u - v‖ ^ 2 + (a - b) ^ 2) ≤ dist x y := by
  rcases lt_trichotomy a b with h | rfl | h
  · rw [norm_sub_rev, ← neg_sub b a, neg_sq, dist_comm]
    exact upper_flat_dist_le_of_lt flat ha h hy hx
  · simpa [Real.sqrt_sq (norm_nonneg (u - v))] using upper_flat_dist_le_of_eq flat hx hy
  · exact upper_flat_dist_le_of_lt flat hb h hx hy

/-- Squared version in metric coordinates, for use with CAT(0) comparison. -/
theorem euclidean_halfSpace_dist_sq_le (flat : E → X) {x y : X} {u v : E} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ w, dist x (flat w) ^ 2 = dist u w ^ 2 + a ^ 2)
    (hy : ∀ w, dist y (flat w) ^ 2 = dist v w ^ 2 + b ^ 2) :
    dist u v ^ 2 + (a - b) ^ 2 ≤ dist x y ^ 2 := by
  have root {q : X} {v : E} {c : ℝ}
      (hq : ∀ w, dist q (flat w) ^ 2 = dist v w ^ 2 + c ^ 2) (w : E) :
      dist q (flat w) = Real.sqrt (‖v - w‖ ^ 2 + c ^ 2) := by
    rw [← dist_eq_norm, ← hq, Real.sqrt_sq dist_nonneg]
  have h := euclidean_halfSpace_dist_le flat ha hb (root hx) (root hy)
  rw [← dist_eq_norm] at h
  simpa only [Real.sq_sqrt (by positivity : 0 ≤ dist u v ^ 2 + (a - b) ^ 2)] using (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mpr h

end SpectralBooks
end LinearAlgebra
end OAI
