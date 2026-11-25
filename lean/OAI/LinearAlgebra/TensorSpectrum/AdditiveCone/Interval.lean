import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Reconstruction of one rational variable

The compatibility conditions produced by eliminating one variable from a finite
system of affine inequalities suffice to reconstruct that variable over `ℚ`.
-/

namespace OAI.LinearAlgebra.TensorSpectrum

/-- The one-variable reconstruction step of Fourier--Motzkin elimination.
Zero coefficients require a nonnegative constant, and each positive/negative
pair requires a nonnegative elimination combination. These conditions suffice
for a rational solution to every original inequality. -/
theorem exists_nonneg_affine_of_pairwise {ι : Type*} [Fintype ι]
    (a b : ι → ℚ)
    (hzero : ∀ i, a i = 0 → 0 ≤ b i)
    (hpair : ∀ i j, 0 < a i → a j < 0 →
      0 ≤ (-a j) * b i + a i * b j) :
    ∃ x : ℚ, ∀ i, 0 ≤ a i * x + b i := by
  classical
  let P : Finset ι := Finset.univ.filter (fun i => 0 < a i)
  by_cases hP : P.Nonempty
  · obtain ⟨p, hpP, hmax⟩ := P.exists_max_image (fun i => -b i / a i) hP
    have hp : 0 < a p := (Finset.mem_filter.mp hpP).2
    have hpx : a p * (-b p / a p) = -b p :=
      mul_div_cancel₀ _ (ne_of_gt hp)
    refine ⟨-b p / a p, ?_⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hprod : 0 ≤ a p * (a i * (-b p / a p) + b i) := by
        calc
          0 ≤ (-a i) * b p + a p * b i := hpair p i hp hi
          _ = a i * (a p * (-b p / a p)) + a p * b i := by
            rw [hpx]
            ring
          _ = a p * (a i * (-b p / a p) + b i) := by ring
      exact nonneg_of_mul_nonneg_right hprod hp
    · simpa [hi] using hzero i hi
    · have hiP : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hbound : -b i ≤ a i * (-b p / a p) :=
        (div_le_iff₀' hi).mp (hmax i hiP)
      linarith only [hbound]
  · have hnonpos : ∀ i, a i ≤ 0 := by
      intro i
      apply le_of_not_gt
      intro hi
      exact hP ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let N : Finset ι := Finset.univ.filter (fun i => a i < 0)
    by_cases hN : N.Nonempty
    · obtain ⟨n, hnN, hmin⟩ := N.exists_min_image (fun i => -b i / a i) hN
      refine ⟨-b n / a n, ?_⟩
      intro i
      by_cases hi : a i < 0
      · have hiN : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hbound : -b i ≤ a i * (-b n / a n) :=
          (le_div_iff_of_neg' hi).mp (hmin i hiN)
        linarith only [hbound]
      · have hi0 : a i = 0 := le_antisymm (hnonpos i) (le_of_not_gt hi)
        simpa [hi0] using hzero i hi0
    · refine ⟨0, ?_⟩
      intro i
      have hnonneg : 0 ≤ a i := by
        apply le_of_not_gt
        intro hi
        exact hN ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
      have hi0 : a i = 0 := le_antisymm (hnonpos i) hnonneg
      simpa using hzero i hi0

end OAI.LinearAlgebra.TensorSpectrum
