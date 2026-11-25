import OAI.LinearAlgebra.SpectralBooks.ConeTranslate

namespace OAI
/-! # Pairing along an oriented cone axis -/

namespace LinearAlgebra.SpectralBooks

open HyperbolicObstruction

variable {X : Type*} [MetricSpace X] (T : ConeData X) (h : CATZero X)

/-- Translating two points of the parallel set gives the bilinear expansion
of their pairing, for arbitrary signed translation parameters. -/
theorem pairing_signedTranslates {c d x y : X} (hop : T.Opposite c d)
    (hx : T.Parallel c d x) (hy : T.Parallel c d y) (s t : ℝ) :
    T.pairing (signedTranslate T h c d s x) (signedTranslate T h c d t y) =
      T.pairing x y + s * T.pairing c y + t * T.pairing c x + s * t * T.normSq c := by
  have hdx : T.pairing d x = -T.pairing c x := by
    unfold ConeData.Parallel at hx
    linarith
  have hdy : T.pairing d y = -T.pairing c y := by
    unfold ConeData.Parallel at hy
    linarith
  by_cases hs : 0 ≤ s <;> by_cases ht : 0 ≤ t
  · simpa only [signedTranslate, hs, ht, ↓reduceIte] using
      T.pairing_translates_same h hop hx hy hs ht
  · simp only [signedTranslate, hs, ht, ↓reduceIte,
      T.pairing_translates_opposite h hop hx hy hs (neg_nonneg.mpr (le_of_not_ge ht))]
    ring
  · simp only [signedTranslate, hs, ht, ↓reduceIte,
      T.pairing_translates_opposite h (hop.symm T) (hx.symm T) (hy.symm T)
        (neg_nonneg.mpr (le_of_not_ge hs)) ht, hdx, hdy, ← hop.1]
    ring
  · simp only [signedTranslate, hs, ht, ↓reduceIte,
      T.pairing_translates_same h (hop.symm T) (hx.symm T) (hy.symm T)
        (neg_nonneg.mpr (le_of_not_ge hs)) (neg_nonneg.mpr (le_of_not_ge ht)),
      hdx, hdy, ← hop.1]
    ring

end LinearAlgebra.SpectralBooks

end OAI
