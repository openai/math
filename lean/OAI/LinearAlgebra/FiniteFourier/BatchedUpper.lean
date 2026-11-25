import OAI.LinearAlgebra.FiniteFourier.Batched
import OAI.LinearAlgebra.FiniteFourier.CompanionUpper

/-! # The uniform gate upper bound for independent Fourier transforms -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

universe u v

/-- Every batch size uses the same constant, including when the groups and the
directions of the transforms vary from one coordinate block to the next. -/
theorem batchFourier_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ {n J : ℕ} (K : Type v) [Field K]
      (B : Fin J → FourierBlock.{u,v} K n), 2 ≤ n →
      (complexity (batchMatrix B) : ℝ) ≤ C * (J * (n : ℝ)) *
        (1 + Real.logb 2 n) ^ ((1 : ℝ) / 2 + ε) := by
  obtain ⟨C, hC, bound⟩ := fourierComplexity_upper.{u,v} hε
  refine ⟨C, hC, ?_⟩
  intro n J K _ B hn
  have localBound (j : Fin J) :
      (complexity (B j).matrix : ℝ) ≤
        C * n * (1 + Real.logb 2 n) ^ ((1 : ℝ) / 2 + ε) := by
    have h := bound (B j).G K (B j).admissible (by simpa only [FourierBlock.card_group] using hn)
    dsimp only at h
    rw [(B j).card_group] at h
    unfold FourierBlock.matrix
    split <;> rw [complexity_reindex]
    · exact h.2
    · exact h.1
  calc
    (complexity (batchMatrix B) : ℝ) ≤ ∑ j, (complexity (B j).matrix : ℝ) := by
      exact_mod_cast complexity_batchMatrix_le_sum B
    _ ≤ ∑ _j : Fin J, C * n * (1 + Real.logb 2 n) ^ ((1 : ℝ) / 2 + ε) :=
      Finset.sum_le_sum fun j _ => localBound j
    _ = _ := by simp; ring

end FiniteFourier
end LinearAlgebra
end OAI
