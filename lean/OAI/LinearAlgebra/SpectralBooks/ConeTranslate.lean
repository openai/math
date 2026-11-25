import OAI.Geometry.HyperbolicGroups.CATZero

/-! Signed translations along an axis in a CAT(0) cone. -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open HyperbolicObstruction

variable {X : Type*} [MetricSpace X] (T : ConeData X) (h : CATZero X)

/-- Translate by a signed amount along the axis whose ends are `c` and `d`. -/
noncomputable def signedTranslate (c d : X) (t : ℝ) (x : X) : X :=
  if 0 ≤ t then T.translate h c t x else T.translate h d (-t) x

/-- On the parallel set, the pairing is affine in the signed displacement. -/
theorem pairing_signedTranslate {c d x y : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) (hy : T.Parallel c d y) (t : ℝ) :
    T.pairing x (signedTranslate T h c d t y) = T.pairing x y + t * T.pairing c x := by
  by_cases ht : 0 ≤ t
  · simp only [signedTranslate, ht, ↓reduceIte]
    exact T.pairing_translate h hop hx hy ht
  · simp only [signedTranslate, ht, ↓reduceIte]
    rw [T.pairing_translate h (hop.symm T)
      (hx.symm T) (hy.symm T) (neg_nonneg.mpr (le_of_not_ge ht))]
    have he : T.pairing d x = -T.pairing c x := by
      unfold ConeData.Parallel at hx
      linarith
    rw [he, neg_mul_neg]

/-- The pairings of signed translates split off a Euclidean coordinate when
both base points are orthogonal to the axis. -/
theorem pairing_signedTranslates_of_orthogonal {c d x y : X} (hop : T.Opposite c d)
    (hc : T.normSq c = 1) (hcx : T.pairing c x = 0) (hdx : T.pairing d x = 0)
    (hcy : T.pairing c y = 0) (hdy : T.pairing d y = 0) (s t : ℝ) :
    T.pairing (signedTranslate T h c d s x) (signedTranslate T h c d t y) =
      T.pairing x y + s * t := by
  have hx : T.Parallel c d x := by simp [ConeData.Parallel, hcx, hdx]
  have hy : T.Parallel c d y := by simp [ConeData.Parallel, hcy, hdy]
  have hd : T.normSq d = 1 := hop.1.symm.trans hc
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
  · simp [signedTranslate, hs, ht, T.pairing_translates_same h hop hx hy hs ht, hcy, hcx, hc]
  · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    simp [signedTranslate, hs, ht, T.pairing_translates_opposite h hop hx hy hs ht', hcy, hcx, hc]
  · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    simp [signedTranslate, hs, ht, T.pairing_translates_opposite h (hop.symm T) (hx.symm T)
      (hy.symm T) hs' ht, hdy, hdx, hd]
  · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
    simp [signedTranslate, hs, ht, T.pairing_translates_same h (hop.symm T) (hx.symm T)
      (hy.symm T) hs' ht', hdy, hdx, hd]

end SpectralBooks
end LinearAlgebra
end OAI
