import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowMean

/-! # Concentration of the shifted digit count

Under independent uniform shifts, the centered least representatives have
range width ℓ − 1. Hoeffding's inequality applied to their sum and its negative
gives a two-sided tail bound.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable section

/-- Independent uniform shifts of the radix digits. -/
def uniformShiftMeasure (ℓ m : ℕ) [NeZero ℓ] : Measure (Fin m → ZMod ℓ) :=
  Measure.pi fun _ => uniformOn Set.univ

instance (ℓ m : ℕ) [NeZero ℓ] : IsProbabilityMeasure (uniformShiftMeasure ℓ m) := by
  unfold uniformShiftMeasure
  infer_instance

variable {ℓ m : ℕ} [NeZero ℓ]

/-- Two-sided Hoeffding bound for the sum of the shifted least representatives. -/
theorem shiftedCount_tail (k : Fin m → ZMod ℓ)
    {B : ℝ} (hB : 0 ≤ B) :
    (uniformShiftMeasure ℓ m).real {β |
      B ≤ |(∑ j, ((k j + β j).val : ℝ)) - (m : ℝ) * ((ℓ : ℝ) - 1) / 2|} ≤
      2 * Real.exp (-2 * B ^ 2 / ((m : ℝ) * ((ℓ : ℝ) - 1) ^ 2)) := by
  let μ := uniformShiftMeasure ℓ m
  let Y (j : Fin m) (z : ZMod ℓ) : ℝ := (k j + z).val
  let X (j : Fin m) (z : ZMod ℓ) : ℝ := Y j z - ((ℓ : ℝ) - 1) / 2
  let c : ℝ≥0 := (‖(ℓ : ℝ) - 1‖₊ / 2) ^ 2
  have h : ∀ j : Fin m, HasSubgaussianMGF (fun β : Fin m → ZMod ℓ => X j (β j)) c μ := by
    intro j
    have hy (z : ZMod ℓ) : Y j z ∈ Set.Icc 0 ((ℓ : ℝ) - 1) := by
      refine ⟨Nat.cast_nonneg _, ?_⟩
      have hz : (k j + z).val + 1 ≤ ℓ := (k j + z).val_lt
      change ((k j + z).val : ℝ) ≤ _
      exact le_sub_iff_add_le.mpr (by exact_mod_cast hz)
    have hg := hasSubgaussianMGF_of_mem_Icc
      (μ := uniformOn Set.univ) (measurable_of_finite (Y j)).aemeasurable
      (ae_of_all _ hy)
    change HasSubgaussianMGF (X j ∘ (fun β : Fin m → ZMod ℓ => β j)) c (Measure.pi fun _ => uniformOn Set.univ)
    apply HasSubgaussianMGF.of_map (measurable_pi_apply j).aemeasurable
    rw [(measurePreserving_eval (fun _ : Fin m => uniformOn (Set.univ : Set (ZMod ℓ))) j).map_eq]
    simpa only [sub_zero, X, integral_shiftedDigit (k j), Y, c] using hg
  have hind : iIndepFun (fun (j : Fin m) (β : Fin m → ZMod ℓ) => X j (β j)) μ :=
    iIndepFun_pi (μ := fun _ : Fin m => uniformOn (Set.univ : Set (ZMod ℓ)))
      (fun i => (measurable_of_finite (X i)).aemeasurable)
  let T (β : Fin m → ZMod ℓ) := ∑ j, X j (β j)
  have hsum : HasSubgaussianMGF T (∑ _ : Fin m, c) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hind (fun i _ => h i)
  have ht (β) : T β = (∑ j, ((k j + β j).val : ℝ)) - (m : ℝ) * ((ℓ : ℝ) - 1) / 2 := by
    simp [T, X, Y, Finset.sum_sub_distrib, mul_div_assoc]
  have hset : {β | B ≤ |(∑ j, ((k j + β j).val : ℝ)) - (m : ℝ) * ((ℓ : ℝ) - 1) / 2|} =
      {β | B ≤ T β} ∪ {β | B ≤ (-T) β} := by
    ext β
    simp only [Set.mem_ofPred_eq, Set.mem_union, ← ht, Pi.neg_apply, le_abs]
  have hℓ : (1 : ℝ) ≤ ℓ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
  have he : -B ^ 2 / (2 * ((∑ _ : Fin m, c : ℝ≥0) : ℝ)) =
      -2 * B ^ 2 / ((m : ℝ) * ((ℓ : ℝ) - 1) ^ 2) := by
    have hd : 2 * ((∑ _ : Fin m, c : ℝ≥0) : ℝ) =
        ((m : ℝ) * ((ℓ : ℝ) - 1) ^ 2) / 2 := by
      simp [c, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hℓ)]
      ring
    rw [hd, div_div_eq_mul_div]
    ring
  rw [hset]
  apply (measureReal_union_le _ _).trans
  have hp := hsum.measure_ge_le hB
  have hn := hsum.neg.measure_ge_le hB
  rw [he] at hp hn
  linarith

end

end FiniteFourier
end LinearAlgebra
end OAI
