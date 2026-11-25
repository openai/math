import OAI.LinearAlgebra.SpectralBooks.KroneckerRank
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Rank charged to a change of time shift in binary feedback

If two time operators differ in rank one, changing the operator after every
state costs at most one rank per state, independent of the number of time slots.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier
open Matrix
open scoped Kronecker

variable {K S I O D : Type*} [Field K] [Fintype S] [Fintype I] [Fintype D]
  [DecidableEq S] [DecidableEq D]

/-- Resolvent identity in rank form, allowing rectangular input and output sets. -/
theorem rank_feedback_difference (C Z Z₀ : Matrix S S K) (T V V₀ : Matrix S I K)
    (h : (1 - Z * C).det ≠ 0) (hv : V = Z * (C * V + T))
    (hv₀ : V₀ = Z₀ * (C * V₀ + T)) :
    (V - V₀).rank ≤ (Z - Z₀).rank := by
  have stateEq : V - Z * (C * V) = Z * T := by
    rw [sub_eq_iff_eq_add]
    simpa only [Matrix.mul_add, add_comm] using hv
  have identity : (1 - Z * C) * (V - V₀) = (Z - Z₀) * (C * V₀ + T) := by
    calc
      _ = (V - Z * (C * V)) - V₀ + Z * (C * V₀) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
        abel
      _ = _ := by
        rw [stateEq, Matrix.sub_mul]
        conv_lhs => enter [1, 2]; rw [hv₀]
        simp only [Matrix.mul_add]
        abel
  calc
    _ = ((1 - Z * C) * (V - V₀)).rank := (rank_mul_eq_right_of_det_ne_zero _ _ h).symm
    _ ≤ _ := identity ▸ rank_mul_le_left _ _

/-- In the time-dilated system the same shift is applied at each state. An arbitrary
linear readout from the states preserves the one-rank-per-state estimate. -/
theorem rank_time_shift_readout (C : Matrix (S × D) (S × D) K) (R R₀ : Matrix D D K)
    (T V V₀ : Matrix (S × D) I K) (U : Matrix O (S × D) K)
    (hr : (R - R₀).rank ≤ 1) (h : (1 - ((1 : Matrix S S K) ⊗ₖ R) * C).det ≠ 0)
    (hv : V = ((1 : Matrix S S K) ⊗ₖ R) * (C * V + T))
    (hv₀ : V₀ = ((1 : Matrix S S K) ⊗ₖ R₀) * (C * V₀ + T)) :
    (U * V - U * V₀).rank ≤ Fintype.card S := by
  rw [← Matrix.mul_sub]
  apply (rank_mul_le_right _ _).trans
  apply (rank_feedback_difference _ _ _ _ _ _ h hv hv₀).trans
  have diff : (1 : Matrix S S K) ⊗ₖ R - (1 : Matrix S S K) ⊗ₖ R₀ =
      (1 : Matrix S S K) ⊗ₖ (R - R₀) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    exact (mul_sub ((1 : Matrix S S K) i j) (R a b) (R₀ a b)).symm
  rw [diff, OAI.LinearAlgebra.SpectralBooks.rank_kronecker, rank_one]
  simpa using Nat.mul_le_mul_left (Fintype.card S) hr

end FiniteFourier
end LinearAlgebra
end OAI
