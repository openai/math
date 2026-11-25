import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import OAI.LinearAlgebra.SpectralBooks.PowerSpanDimension
import OAI.LinearAlgebra.SpectralBooks.SpanValue

/-! # Zariski closed sublevels of finite-site spectral values

For finitely many sites in a fixed format, the degree-`n` powers of points
of a set lie in the span of a polynomial number of powers of its members.
The span includes the powers of all points in its Zariski closure. Taking
`n`th roots eliminates the polynomial factor in the spectral evaluation.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped NNReal

namespace SiteTensor

universe v

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
  {A : I → Type v} [∀ i, Fintype (A i)]
  (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))

/-- A fixed-format spectral value bound on a set persists on its Zariski
closure. This holds for the points of the actual restriction-class semiring. -/
theorem coeffValue_le_of_mem_closure {S : Set ((∀ i, A i) → K)} {T : (∀ i, A i) → K}
    (hT : T ∈ affineZariskiClosure S) {b : ℝ≥0} (hb : ∀ Y ∈ S, coeffValue φ Y ≤ b) :
    coeffValue φ T ≤ b := by
  classical
  apply nnreal_le_of_pow_le_polynomial_mul_pow (Fintype.card (∀ i, A i))
  intro n _
  obtain ⟨s, hs, hcard, hspan⟩ := exists_finset_coordinatePower_span n S
  have hmem := coordinatePower_mem_span_of_closure hT n
  rw [← hspan] at hmem
  let U (y : s) := groupedPower n y.val
  let regroup : ((Fin n → ∀ i, A i) → K) →ₗ[K] ((∀ i, Fin n → A i) → K) :=
    { toFun := fun f x ↦ f (fun j i ↦ x i j)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hle : Submodule.span K (coordinatePower n '' (s : Set _)) ≤
      (Submodule.span K (Set.range U)).comap regroup := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
  have hgroup : groupedPower n T ∈ Submodule.span K (Set.range U) := hle hmem
  calc
    _ = coeffValue φ (groupedPower n T) := (coeffValue_groupedPower φ n T).symm
    _ ≤ (s.card : ℝ≥0) * b ^ n := by
      have hv (y : s) : coeffValue φ (U y) ≤ b ^ n := by
        rw [show U y = groupedPower n y.val from rfl, coeffValue_groupedPower]
        exact pow_le_pow_left' (hb y (hs y.property)) _
      simpa only [Fintype.card_coe] using coeffValue_span_le φ U hgroup hv
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- Closedness of the value sublevel itself. -/
theorem affineZariskiClosure_coeffValue_sublevel (b : ℝ≥0) :
    affineZariskiClosure {T : (∀ i, A i) → K | coeffValue φ T ≤ b} =
      {T | coeffValue φ T ≤ b} :=
  Set.Subset.antisymm (fun _ hT ↦ coeffValue_le_of_mem_closure φ hT (fun _ h ↦ h))
    (subset_affineZariskiClosure _)

/-- Closure of scaled base-two log-price sublevels at nonzero tensors,
including the collapsed price of scale zero. -/
theorem logPrice_le_of_mem_closure {S : Set ((∀ i, A i) → K)} {T : (∀ i, A i) → K}
    (hT : T ∈ affineZariskiClosure S) (hne : T ≠ 0) {c b : ℝ} (hc : 0 ≤ c)
    (hb : ∀ Y ∈ S, Y ≠ 0 → c * Real.logb 2 (coeffValue φ Y : ℝ) ≤ b) :
    c * Real.logb 2 (coeffValue φ T : ℝ) ≤ b := by
  have hpos {Y : (∀ i, A i) → K} (hY : Y ≠ 0) : 0 < (coeffValue φ Y : ℝ) := by
    exact_mod_cast zero_lt_one.trans_le (coeffValue_one_le φ hY)
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul] at hb ⊢
    by_contra! h
    have hz : coeffValue φ T ≤ 0 := coeffValue_le_of_mem_closure φ hT (by
      intro Y hY
      by_cases h0 : Y = 0
      · simp [h0]
      · exact False.elim (h.not_ge (hb Y hY h0)))
    exact (not_lt_of_ge hz) (zero_lt_one.trans_le (coeffValue_one_le φ hne))
  · let B : ℝ≥0 := ⟨(2 : ℝ) ^ (b / c), Real.rpow_nonneg (by norm_num) _⟩
    have bound (Y : (∀ i, A i) → K) (hY : Y ≠ 0) :
        c * Real.logb 2 (coeffValue φ Y : ℝ) ≤ b ↔ coeffValue φ Y ≤ B := by
      rw [mul_comm, ← le_div_iff₀ hc, Real.logb_le_iff_le_rpow (by norm_num) (hpos hY)]
      rfl
    apply (bound T hne).mpr (coeffValue_le_of_mem_closure φ hT ?_)
    intro Y hY
    by_cases h0 : Y = 0
    · simp [h0]
    · exact (bound Y h0).mp (hb Y hY h0)

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
