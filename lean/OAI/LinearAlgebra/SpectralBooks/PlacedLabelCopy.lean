import OAI.LinearAlgebra.SpectralBooks.CopyLabelGroundField
import OAI.LinearAlgebra.SpectralBooks.Prices
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

/-! # Cost of copying a label at a spectral placement

This is the common-label copying lemma used for planar networks (CD, Lemma
`opposite-copy`). The placement can contain collisions. The price of the
three-site diagonal supplies the copy and the independent returned wire
subtracts its distance from that cost.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SpectralPlacementPrices

open SiteTensor

noncomputable section
variable {I : Type} [Fintype I] {X K : Type*} [MetricSpace X] [Field K]

/-- If a tensor carries the same label at the first two sites on its support,
the price increase of copying it to the third site is bounded by the
diagonal increment times the logarithm of the label size. -/
theorem copyLabel_price_le (P : SpectralPlacementPrices K X) (T : Raw.{0} I K) (x : I → X)
    (σ : Fin 3 → I) {q : ℕ} (hq : 0 < q)
    (hA : T.Leg (σ 0) → Fin q) (hB : T.Leg (σ 1) → Fin q)
    (hm : ∀ z, T.coeff z ≠ 0 → hA (z (σ 0)) = hB (z (σ 1))) :
    P.price (T.appendLabel (σ 2) (Fin q) (fun z => hA (z (σ 0)))) x ≤ P.price T x +
      (P.price (Raw.diagonal (Fin 3) K (Fin 2)) (x ∘ σ) -
        dist (x (σ 0)) (x (σ 1))) * Real.logb 2 q := by
  let : Nonempty I := ⟨σ 0⟩
  let w : Fin 2 → I := ![σ 0, σ 1]
  have hw : dist (x (σ 0)) (x (σ 1)) = P.price (Raw.diagonal (Fin 2) K (Fin 2)) (x ∘ w) :=
    (P.wire (x ∘ w)).symm
  rw [hw]
  rcases P.zero_or_common_group_price x with h | ⟨φ, c, hc, h⟩
  · have hz (Z : Raw.{0} I K) : P.price Z x = 0 := h Z id
    simp only [hz, h, sub_self, zero_mul, add_zero, le_refl]
  · have hprice (Z : Raw.{0} I K) : P.price Z x = rawLogPrice φ c Z := by
      have he := congrArg (fun a : TensorClass I K => c * Real.logb 2 (φ.val a : ℝ))
        (ofRaw_eq_iff.mpr Z.group_id_equivalent)
      exact (h Z id).trans he
    rw [hprice, hprice, h, h]
    exact rawLogPrice_copy φ c hc.le T σ hq hA hB hm

end
end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
