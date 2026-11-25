import OAI.Computability.BorderVNP.CoverFrameProducts

/-!
# Exact finite rational expansion of independently sampled frame motions

One sample chooses a word length and the letters of the word. A product sample chooses
one such word per factor. Distinct samples that reach the same point contribute separately,
as they do in the Cesàro law.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Hecke

open MeasureTheory Set Finset
open scoped ENNReal Classical

variable {G I : Type*} [Group G] (Γ : Subgroup G) (z : G)
    [Fintype (Cosets (intersection Γ z))] [Fintype I]

/-- Words for a simultaneous motion, one independent word for each factor. -/
abbrev ProductSample (I : Type*) (n : ℕ) := I → Samples (Cosets (intersection Γ z)) n

/-- Exact rational probability of a tuple of motion words. -/
noncomputable def productWeight (n : ℕ) (w : ProductSample Γ z I n) : ℚ :=
  ∏ i, weight _ n (w i)

/-- Every tuple of words in the product support has positive probability. -/
theorem productWeight_pos (n : ℕ) (w : ProductSample Γ z I n) : 0 < productWeight Γ z n w := by
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  exact Finset.prod_pos fun i _ => weight_pos n (w i)

/-- The rational probabilities of all independent word tuples add to one. -/
theorem sum_productWeight (n : ℕ) : ∑ w : ProductSample Γ z I n, productWeight Γ z n w = 1 := by
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  simp [productWeight, ← Fintype.prod_sum, sum_weight]

/-- Images of the starting frames under the actual tuple of words. -/
noncomputable def productPoint (n : ℕ) (x : I → G) (w : ProductSample Γ z I n) : I → Cosets Γ :=
  fun i => coset Γ (motion (step Γ z) (w i).1 (w i).2 * x i)

variable [MeasurableSpace (Cosets Γ)]

/-- The actual independent product of Cesàro word laws is the finite sum of the rationally
weighted Dirac masses of simultaneous motions. -/
theorem productLaw_eq_samples (n : ℕ) (x : I → G) :
    (productLaw Γ z n x).toMeasure =
      ∑ w : ProductSample Γ z I n, ENNReal.ofReal (productWeight Γ z n w : ℝ) •
        Measure.dirac (productPoint Γ z n x w) := by
  classical
  have : Nonempty (Cosets (intersection Γ z)) := ⟨coset _ 1⟩
  change Measure.pi (fun i => (wordLaw Γ z n (x i)).toMeasure) = _
  apply Measure.pi_eq
  intro S hS
  have hbox := MeasurableSet.univ_pi hS
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hbox]
  simp only [wordLaw, ProbabilityMeasure.coe_mk, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ (hS _), Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hweight : ENNReal.ofReal (productWeight Γ z n w : ℝ) =
      ∏ i, ENNReal.ofReal (weight _ n (w i) : ℝ) := by
    simp only [productWeight, Rat.cast_prod]
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => Rat.cast_nonneg.mpr (weight_pos ..).le
  by_cases h : ∀ i, productPoint Γ z n x w i ∈ S i
  · rw [Set.indicator_of_mem (Set.mem_univ_pi.mpr h), Pi.one_apply, mul_one, hweight]
    apply Finset.prod_congr rfl
    intro i _
    simp only [productPoint] at h
    rw [Set.indicator_of_mem (h i), Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (fun hs => h (Set.mem_univ_pi.mp hs)), mul_zero]
    push Not at h
    obtain ⟨i,hi⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [productPoint] at hi
    rw [Set.indicator_of_notMem hi, mul_zero]

/-- Probability of any measurable event is its finite rational weighted indicator sum.
The statement includes tests pulled back from position, direction, or crossing bins. -/
theorem productLaw_real (n : ℕ) (x : I → G) (B : Set (I → Cosets Γ)) (hB : MeasurableSet B) :
    (productLaw Γ z n x).toMeasure.real B =
      ∑ w : ProductSample Γ z I n, (productWeight Γ z n w : ℝ) *
        B.indicator 1 (productPoint Γ z n x w) := by
  rw [Measure.real, productLaw_eq_samples]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hB]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro w _
    by_cases h : productPoint Γ z n x w ∈ B <;>
      simp [h, Rat.cast_nonneg.mpr (productWeight_pos Γ z n w).le]
  · intro w _
    by_cases h : productPoint Γ z n x w ∈ B <;> simp [h]

end Hecke

end BorderVNP
end Computability
end OAI
