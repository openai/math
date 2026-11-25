import OAI.LinearAlgebra.FiniteFourier.GridUpperStatement

/-! # Extending the eventual grid upper bound to every size -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter

universe v

/-- The naive row-by-row circuit gives a uniform bound below the size threshold
of the auxiliary-prime and extension-capacity construction. -/
theorem uniformGridUpper_of_eventually
    (h : ∀ α : ℝ, 1 / 2 < α → ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (K : Type v) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
        (T : ∀ i, Matrix (Fin (a i)) (Fin (a i)) K), (∀ i, 2 ≤ a i) →
        (∀ i, GridFactor (T i)) → (∏ i, a i) = N →
        (complexity (gridTensor T) : ℝ) ≤ C * N * (1 + Real.logb 2 N) ^ α) :
    UniformGridUpper.{v} := by
  intro α hα
  obtain ⟨C, hC, he⟩ := h α hα
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  let D := max C (N₀ : ℝ)
  refine ⟨D, hC.trans_le (le_max_left ..), ?_⟩
  intro K _ ι _ _ a T ha hT
  let N := ∏ i, a i
  have hpos : 0 < N := Finset.prod_pos (fun i _ ↦ by have := ha i; omega)
  have hpos' : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.logb 2 N := Real.logb_nonneg (by norm_num) (by exact_mod_cast hpos)
  have hw : 1 ≤ (1 + Real.logb 2 N) ^ α :=
    Real.one_le_rpow (by linarith) (by linarith : 0 ≤ α)
  change (complexity (gridTensor T) : ℝ) ≤ D * N * (1 + Real.logb 2 N) ^ α
  by_cases hN : N₀ ≤ N
  · exact (hN₀ N hN K ι a T ha hT rfl).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) hpos') (by linarith))
  · have hnaive : complexity (gridTensor T) ≤ N * N := by
      simpa [N, Fintype.card_pi] using
        (complexity_le_iff ..).mpr (realizableAtMost_card_mul_card (gridTensor T))
    have hND : (N : ℝ) ≤ D := (show (N : ℝ) ≤ N₀ by exact_mod_cast (lt_of_not_ge hN).le).trans
      (le_max_right ..)
    calc
      (complexity (gridTensor T) : ℝ) ≤ N * (N : ℝ) := by exact_mod_cast hnaive
      _ ≤ D * N := mul_le_mul_of_nonneg_right hND hpos'
      _ ≤ D * N * (1 + Real.logb 2 N) ^ α := le_mul_of_one_le_right
        (mul_nonneg (hpos'.trans hND) hpos') hw

end FiniteFourier
end LinearAlgebra
end OAI
