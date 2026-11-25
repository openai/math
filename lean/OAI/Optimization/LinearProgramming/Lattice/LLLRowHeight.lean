import OAI.Optimization.LinearProgramming.Lattice.LLL
import OAI.Optimization.LinearProgramming.Lattice.SizeReduction

/-! Uniform row heights from the bounded Gram determinants inside LLL. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open Finset InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- A single size-reduced row has norm at most the number of basis vectors times
the common bound on the Gram–Schmidt lengths. Other rows need not satisfy Lovász. -/
theorem sizeReduced_row_height (b : Fin (p+1) → E) (i : Fin (p+1)) {K : ℝ}
    (hK : 0 ≤ K) (hg : ∀ j, ‖gramSchmidt ℝ b j‖ ≤ K)
    (hs : ∀ j < i, |gsCoeff b i j| ≤ 1 / 2) :
    ‖b i‖ ≤ (p+1 : ℕ) * K := by
  have hd := gramSchmidt_def'' ℝ b i
  change b i = gramSchmidt ℝ b i + ∑ j ∈ Iio i, gsCoeff b i j • gramSchmidt ℝ b j at hd
  have hs' (j : Fin (p+1)) (hj : j ∈ Iio i) :
      ‖gsCoeff b i j • gramSchmidt ℝ b j‖ ≤ K := by
    rw [norm_smul, Real.norm_eq_abs]
    have ha : |gsCoeff b i j| ≤ 1 := (hs j (mem_Iio.mp hj)).trans (by norm_num)
    simpa using mul_le_mul ha (hg j) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hcard : (Iio i).card + 1 ≤ p+1 := by
    have h := Finset.card_le_univ (insert i (Iio i))
    simpa using h
  calc
    ‖b i‖ = ‖gramSchmidt ℝ b i + ∑ j ∈ Iio i, gsCoeff b i j • gramSchmidt ℝ b j‖ := congrArg norm hd
    _ ≤ ‖gramSchmidt ℝ b i‖ + ∑ j ∈ Iio i, ‖gsCoeff b i j • gramSchmidt ℝ b j‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ K + ∑ _j ∈ Iio i, K := add_le_add (hg _) (Finset.sum_le_sum hs')
    _ = ((Iio i).card + 1 : ℕ) * K := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK

end Lattice
end LinearProgramming
end Optimization
end OAI
