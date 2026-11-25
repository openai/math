import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Tactic
import OAI.LinearAlgebra.SpectralBooks.SpineConditioning

/-!
# The metric of the three-page book

The positive coordinate axes in three-dimensional ℓ¹ realize the metric
tripod. Taking its Euclidean metric product with the spine identifies the
three copies of the spine. We compute the distances used for the three tips
and the two base points in the finite-rank argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

section

open WithLp
open scoped NNReal

/-- The three positive coordinate rays, with their common origin and path metric. -/
abbrev Tripod :=
  {x : PiLp 1 (fun _ : Fin 3 => ℝ) // ∃ (i : Fin 3) (r : ℝ≥0), x = PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ)}

/-- The point at height `r` on arm `i`. -/
def tripodPoint (i : Fin 3) (r : ℝ≥0) : Tripod :=
  ⟨PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ), i, r, rfl⟩

theorem tripodPoint_zero (i j : Fin 3) : tripodPoint i 0 = tripodPoint j 0 := by
  apply Subtype.ext
  change PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (0 : ℝ) = PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (0 : ℝ)
  apply PiLp.ext
  intro k
  simp [PiLp.single_apply]

theorem tripod_dist_same (i : Fin 3) (r s : ℝ≥0) :
    dist (tripodPoint i r) (tripodPoint i s) = |(r : ℝ) - s| := by
  exact PiLp.dist_single_same 1 (fun _ : Fin 3 => ℝ) i (r : ℝ) (s : ℝ)

theorem tripod_dist_of_ne {i j : Fin 3} (hij : i ≠ j) (r s : ℝ≥0) :
    dist (tripodPoint i r) (tripodPoint j s) = (r : ℝ) + s := by
  change dist (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ) : PiLp 1 (fun _ : Fin 3 => ℝ))
    (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (s : ℝ)) = _
  rw [PiLp.dist_eq_of_L1]
  have h (k : Fin 3) : dist (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 i (r : ℝ) k) (PiLp.single (β := fun _ : Fin 3 => ℝ) 1 j (s : ℝ) k) =
      (if k = i then (r : ℝ) else 0) + (if k = j then (s : ℝ) else 0) := by
    by_cases hi : k = i
    · subst k
      simp [hij]
    · by_cases hj : k = j
      · subst k
        simp [hi, Real.dist_eq]
      · simp [hi, hj]
  simp_rw [h]
  simp [Finset.sum_add_distrib]

/-- The book with spine `E`. For Euclidean `E` this has the Euclidean product metric. -/
abbrev Book (E : Type*) := WithLp 2 (Tripod × E)

/-- Page coordinates. Height zero gives the same point in every page. -/
def bookPoint {E : Type*} (i : Fin 3) (r : ℝ≥0) (p : E) : Book E :=
  toLp 2 (tripodPoint i r, p)

theorem bookPoint_zero {E : Type*} (i j : Fin 3) (p : E) :
    bookPoint i 0 p = bookPoint j 0 p := by
  simp only [bookPoint, tripodPoint_zero i j]

theorem book_dist {E : Type*} [PseudoMetricSpace E] (i j : Fin 3) (r s : ℝ≥0) (p q : E) :
    dist (bookPoint i r p) (bookPoint j s q) =
      Real.sqrt ((if i = j then |(r : ℝ) - s| else (r : ℝ) + s) ^ 2 + dist p q ^ 2) := by
  rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
  change (dist (tripodPoint i r) (tripodPoint j s) ^ (2 : ENNReal).toReal +
      dist p q ^ (2 : ENNReal).toReal) ^ (1 / (2 : ENNReal).toReal) = _
  rw [Real.sqrt_eq_rpow]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two]
  by_cases h : i = j
  · subst j
    simp [tripod_dist_same]
  · simp [h, tripod_dist_of_ne h]

theorem book_dist_distinct_tips {E : Type*} [PseudoMetricSpace E] {i j : Fin 3}
    (hij : i ≠ j) (r s : ℝ≥0) (p : E) :
    dist (bookPoint i r p) (bookPoint j s p) = (r : ℝ) + s := by
  rw [book_dist]
  simp only [ite_eq_right_iff.mpr (fun h => (hij h).elim), dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  exact Real.sqrt_sq (add_nonneg r.2 s.2)

/-- The Euclidean triangle with spine endpoints at ±1 and a tip of height `r`
has half-perimeter `1 + √(1 + r²)`. -/
theorem book_triangle_half_perimeter (i : Fin 3) (r : ℝ≥0) :
    (dist (bookPoint i 0 (-1 : ℝ)) (bookPoint i 0 1) +
      dist (bookPoint i 0 (1 : ℝ)) (bookPoint i r 0) +
      dist (bookPoint i r (0 : ℝ)) (bookPoint i 0 (-1))) / 2 =
      1 + Real.sqrt (1 + (r : ℝ) ^ 2) := by
  simp only [book_dist, ite_true, eq_self, NNReal.coe_zero, sub_zero, zero_sub, abs_neg,
    NNReal.abs_eq, Real.dist_eq]
  norm_num [add_comm]
  ring

/-- The signed-height chart through pages `i` and `j`. Nonnegative heights
belong to page `i`, and negative heights belong to page `j`. -/
def bookPlane {E : Type*} (i j : Fin 3) (x : WithLp 2 (E × ℝ)) : Book E :=
  if 0 ≤ x.snd then bookPoint i x.snd.toNNReal x.fst
  else bookPoint j (-x.snd).toNNReal x.fst

theorem bookPlane_nonneg {E : Type*} (i j : Fin 3) (p : E) (r : ℝ≥0) :
    bookPlane i j (toLp 2 (p, (r : ℝ))) = bookPoint i r p := by
  change (if 0 ≤ (r : ℝ) then _ else _) = _
  simp

theorem bookPlane_isometry {E : Type*} [SeminormedAddCommGroup E] {i j : Fin 3} (hij : i ≠ j) :
    Isometry (bookPlane (E := E) i j) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [WithLp.prod_dist_eq_of_L2 x y, add_comm]
  unfold bookPlane
  split_ifs with hx hy hy <;> rw [book_dist]
  · simp [Real.toNNReal_of_nonneg hx, Real.toNNReal_of_nonneg hy, Real.dist_eq]
  · have hny : 0 ≤ -y.snd := by linarith
    simp [hij, Real.toNNReal_of_nonneg hx, Real.toNNReal_of_nonneg hny,
      Real.dist_eq, sq_abs, sub_eq_add_neg]
  · have hnx : 0 ≤ -x.snd := by linarith
    simp only [hij.symm, ite_false, Real.toNNReal_of_nonneg hy, Real.toNNReal_of_nonneg hnx,
      Real.dist_eq, sq_abs, NNReal.coe_mk]
    congr 2
    ring
  · have hnx : 0 ≤ -x.snd := by linarith
    have hny : 0 ≤ -y.snd := by linarith
    simp only [eq_self, ite_true, Real.toNNReal_of_nonneg hnx, Real.toNNReal_of_nonneg hny,
      Real.dist_eq, sq_abs, NNReal.coe_mk]
    congr 2
    ring

/-- A point on the spine of the two-dimensional book. -/
def bookSpine (p : ℝ) : Book ℝ := bookPoint 0 0 p

/-- The two points at coordinates ±1 on the spine. -/
def bookBase : Finset (Book ℝ) := {bookSpine (-1), bookSpine 1}

/-- The tip belonging to party `i` in the rectangular rank test. -/
def bookTip (r : Fin 3 → ℝ≥0) (i : Fin 3) : Book ℝ := bookPoint i (r i) 0

theorem bookTip_dist (r : Fin 3 → ℝ≥0) {i j : Fin 3} (hij : i ≠ j) :
    dist (bookTip r i) (bookTip r j) = (r i : ℝ) + r j :=
  book_dist_distinct_tips hij _ _ _

theorem bookSpine_dist : dist (bookSpine (-1)) (bookSpine 1) = 2 := by
  norm_num [bookSpine, book_dist, Real.dist_eq]

/-- The diagonal price bound of the planar book test, from its metric and
the planar half-perimeter law for each of the three triangles. -/
theorem bookTip_price_le_of_triangle_le {δ : Finset (Book ℝ) → ℝ} (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) (r : Fin 3 → ℝ≥0) (hbase : δ bookBase = 2)
    (htri : ∀ i, δ (insert (bookTip r i) bookBase) ≤
      (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
        dist (bookTip r i) (bookSpine (-1))) / 2) :
    δ (Finset.univ.image (bookTip r)) ≤ ∑ i, Real.sqrt (1 + (r i : ℝ) ^ 2) - 1 := by
  have hB : bookBase.Nonempty := ⟨bookSpine (-1), by simp [bookBase]⟩
  have h := conditioning_image_le hmono hsub hB Finset.univ (bookTip r)
  have htriangle (i : Fin 3) : δ (insert (bookTip r i) bookBase) ≤
      1 + Real.sqrt (1 + (r i : ℝ) ^ 2) := by
    apply (htri i).trans_eq
    simpa only [bookSpine, bookTip, bookPoint_zero i 0] using book_triangle_half_perimeter i (r i)
  simp only [hbase, Fin.sum_univ_three] at h ⊢
  linarith [htriangle 0, htriangle 1, htriangle 2]

theorem bookTip_price_le {δ : Finset (Book ℝ) → ℝ} (hmono : Monotone δ)
    (hsub : IntersectingSubmodular δ) (r : Fin 3 → ℝ≥0) (hbase : δ bookBase = 2)
    (htri : ∀ i, δ (insert (bookTip r i) bookBase) =
      (dist (bookSpine (-1)) (bookSpine 1) + dist (bookSpine 1) (bookTip r i) +
        dist (bookTip r i) (bookSpine (-1))) / 2) :
    δ (Finset.univ.image (bookTip r)) ≤ ∑ i, Real.sqrt (1 + (r i : ℝ) ^ 2) - 1 :=
  bookTip_price_le_of_triangle_le hmono hsub r hbase (fun i => (htri i).le)

private theorem sqrt_scaled_sum_sq (a b c : ℝ) (ha : 0 ≤ a) :
    Real.sqrt ((a * b) ^ 2 + (a * c) ^ 2) = a * Real.sqrt (b ^ 2 + c ^ 2) := by
  rw [show (a * b) ^ 2 + (a * c) ^ 2 = a ^ 2 * (b ^ 2 + c ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Reflect one tip across the common facet. The Euclidean segment from the
reflected tip to the other tip crosses the facet at a point between the feet.
Only distances in each individual page enter this upper bound. -/
theorem dist_le_reflected_path {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [PseudoMetricSpace X] {x y : X} {p q : E} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (facet : E → X)
    (hx : ∀ z ∈ segment ℝ p q, dist x (facet z) = Real.sqrt (dist p z ^ 2 + r ^ 2))
    (hy : ∀ z ∈ segment ℝ p q, dist (facet z) y = Real.sqrt (dist z q ^ 2 + s ^ 2)) :
    dist x y ≤ Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
  let t := r / (r + s)
  have ht : 0 ≤ t := div_nonneg hr (add_nonneg hr hs)
  have ht₁ : t ≤ 1 := by
    rcases (add_nonneg hr hs).eq_or_lt with h | h
    · simp [t, ← h]
    · exact (div_le_one h).mpr (by linarith)
  have hr' : t * (r + s) = r := by
    rcases (add_nonneg hr hs).eq_or_lt with h | h
    · rw [← h, mul_zero]
      linarith
    · exact div_mul_cancel₀ r h.ne'
  have hs' : (1 - t) * (r + s) = s := by linarith
  let z := AffineMap.lineMap p q t
  have hz : z ∈ segment ℝ p q := lineMap_mem_segment ℝ p q ⟨ht, ht₁⟩
  have hx' : dist x (facet z) = t * Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
    rw [hx z hz, dist_left_lineMap, Real.norm_eq_abs, abs_of_nonneg ht]
    conv_lhs => rw [← hr']
    exact sqrt_scaled_sum_sq _ _ _ ht
  have hy' : dist (facet z) y = (1 - t) * Real.sqrt (dist p q ^ 2 + (r + s) ^ 2) := by
    rw [hy z hz, dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁)]
    conv_lhs => rw [← hs']
    exact sqrt_scaled_sum_sq _ _ _ (sub_nonneg.mpr ht₁)
  calc
    dist x y ≤ dist x (facet z) + dist (facet z) y := dist_triangle _ _ _
    _ = _ := by rw [hx', hy']; ring

end

end

end SpectralBooks
end LinearAlgebra
end OAI
