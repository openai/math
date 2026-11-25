import OAI.LinearAlgebra.SpectralBooks.GroupedPower
import OAI.LinearAlgebra.SpectralBooks.PlacementPullback
import OAI.LinearAlgebra.SpectralBooks.PriceOrdinary
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Prices for the exterior-algebra relocation argument

Tensor powers and wire dimensions may change at each depth of the exterior
splitting argument. A fixed finite list of sites supplies one common scaling
factor for the ordinary addition loss throughout the argument.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section
namespace SiteTensor

variable {I J : Type} [Fintype I] [Fintype J] {K : Type*} [Field K]

/-- Group the copies of each leg of a tensor power into one leg. -/
def Raw.powerTensor (T : Raw.{0} I K) (n : ℕ) : Raw.{0} I K :=
  ⟨fun i ↦ Fin n → T.Leg i, fun _ ↦ inferInstance, groupedPower n T.coeff⟩

omit [Fintype I] in
theorem Raw.powerTensor_ne_zero (T : Raw.{0} I K) (hT : T.coeff ≠ 0) (n : ℕ) :
    (T.powerTensor n).coeff ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, T.coeff x ≠ 0 := Function.ne_iff.mp hT
  intro h
  have hz := congrFun h (fun i _ ↦ x i)
  change (∏ _ : Fin n, T.coeff x) = 0 at hz
  exact (Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hx) hz

variable [Nonempty I] [Nonempty J]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)

/-- Every placement multiplies its log price by the exponent of the tensor power. -/
theorem rawLogPrice_group_powerTensor (T : Raw.{0} I K) (σ : I → J) (n : ℕ) :
    rawLogPrice φ c ((T.powerTensor n).group σ) = n * rawLogPrice φ c (T.group σ) := by
  let v := (normalizedSpectrum.toRingHom φ).toMonoidHom.comp (groupMulHom (K := K) σ)
  have he (S : Raw.{0} I K) : φ.val (ofRaw (S.group σ)) = v (ofRaw S) := rfl
  simp only [rawLogPrice, he, Raw.powerTensor, ofRaw_groupedPower, map_pow, NNReal.coe_pow,
    Real.logb_pow]
  ring

/-- A nonzero ordinary sum of two arrays is priced within one normalization
factor of a nonzero summand. The two arrays share their format. -/
theorem rawLogPrice_add_select (hc : 0 ≤ c) {A : J → Type} [∀ j, Fintype (A j)]
    (U V : (∀ j, A j) → K) (hne : U + V ≠ 0) :
    (U ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, U⟩ + c) ∨
    (V ≠ 0 ∧ rawLogPrice φ c ⟨A, inferInstance, U + V⟩ ≤
      rawLogPrice φ c ⟨A, inferInstance, V⟩ + c) := by
  classical
  let T : Fin 2 → (∀ j, A j) → K := ![U,V]
  have hsum : ∑ i, T i = U + V := by simp [T, Fin.sum_univ_two]
  obtain ⟨i, hi, hp⟩ := ordinary_sum_logb_le φ T (hsum ▸ hne) hc
  rw [hsum] at hp
  fin_cases i
  · left
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩
  · right
    exact ⟨hi, by simpa [rawLogPrice, coeffValue, ofCoeffs, T,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hp⟩

end SiteTensor

namespace SpectralPlacementPrices
open SiteTensor

variable {K X : Type*} [Field K] [MetricSpace X] (P : SpectralPlacementPrices K X)

/-- For a finite list of sites, either every grouped price vanishes or one
positively scaled normalized spectral point gives all grouped prices, even
when the original list has repetitions. -/
theorem zero_or_common_group_price {J : Type} [Fintype J] [Nonempty J] (p : J → X) :
    (∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (σ : I → J), P.price T (p ∘ σ) = 0) ∨
    ∃ (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ),
      0 < c ∧ ∀ {I : Type} [Fintype I] (T : Raw.{0} I K) (σ : I → J),
        P.price T (p ∘ σ) = rawLogPrice φ c (T.group σ) := by
  obtain ⟨g, hg, hprice⟩ := P.exists_spectralPrice_of_placement p
  rcases hg with rfl | ⟨φ, c, hc, rfl⟩
  · left
    intro I _ T σ
    simp only [P.group, hprice, classPrice_zero]
  · refine Or.inr ⟨φ, c, hc, ?_⟩
    intro I _ T σ
    rw [P.group, hprice, classPrice_scaled_log]
    rfl

/-- A tensor power at any finite placement, including a collapsed one. -/
theorem price_powerTensor {I : Type} [Fintype I] [Nonempty I] (T : Raw.{0} I K)
    (x : I → X) (n : ℕ) : P.price (T.powerTensor n) x = n * P.price T x := by
  rcases P.zero_or_common_group_price x with h | ⟨φ, c, _, h⟩
  · have hT : P.price T x = 0 := h T id
    rw [hT, mul_zero]
    exact h (T.powerTensor n) id
  · simpa only [Function.comp_id] using (h (T.powerTensor n) id).trans
      ((rawLogPrice_group_powerTensor φ c T id n).trans (congrArg ((n : ℝ) * ·) (h T id).symm))

end SpectralPlacementPrices
end

end

end SpectralBooks
end LinearAlgebra
end OAI
