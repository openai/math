import OAI.Hierarchy.ProbePurchase
import OAI.Hierarchy.ProbeParameters

namespace OAI
/-! # Concrete paper-scale calibration and saving from a dense set of marked chains -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical BigOperators
noncomputable section

/-- The deliberately longer integer chain in the paper allows using the rational
projection threshold T/(4k), avoiding any irrational programmed tests. -/
theorem purchase_constants (k : ℕ) (hk : 0 < k) {T : ℝ} (hT : 0 < T) (small : T ≤ 1) :
    let η := T/(100*k)
    let target := T/(4*k)
    let H := ⌈32*k/T⌉₊
    4*target^2 ≤ T^2/(4*k) ∧ η < target ∧ 1+η < (H:ℝ)*(target-η) := by
  intro η target H
  have realK : 0 < (k:ℝ) := by exact_mod_cast hk
  have oneK : 1 ≤ (k:ℝ) := by exact_mod_cast hk
  have pos : 0 < T/(4*k)-T/(100*k) := by
    field_simp [realK.ne']; nlinarith only [hT, realK]
  have length : 32*(k:ℝ)/T ≤ H := Nat.le_ceil _
  have size := mul_le_mul_of_nonneg_right length pos.le
  have product : 32*(k:ℝ)/T*(T/(4*k)-T/(100*k))=192/25 := by
    field_simp [hT.ne',realK.ne']; ring
  have η_small : η ≤ 1 := by
    apply (div_le_iff₀ (show 0 < 100*(k:ℝ) by positivity)).2
    linarith
  refine ⟨?_,sub_pos.mp pos,?_⟩
  · dsimp only [target]
    have cmp := mul_le_mul_of_nonneg_left oneK (sq_nonneg T)
    field_simp [realK.ne']
    nlinarith only [cmp,oneK]
  · rw [product] at size
    change 1+η < (H:ℝ)*(T/(4*k)-T/(100*k))
    linarith

/-- Exact per-good-chain payment at the unnormalized score. The outer account
charges the physical capacity price and divides by n after all simultaneous buys. -/
theorem per_chain_reward {W N T k : ℝ} (hW : 0 < W) (hN : 0 < N) (hT : 0 < T) (hk : 0 < k) :
    (W⁻¹^4/(N*T^2))*(T^2/(4*k))/8 = W⁻¹^4/(32*k*N) := by
  field_simp [hW.ne',hN.ne',hT.ne',hk.ne']; ring

end
end Hierarchy.AdaptiveProbe

end OAI
