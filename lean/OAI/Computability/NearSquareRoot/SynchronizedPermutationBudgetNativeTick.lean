import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetInput
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetRate
import OAI.Computability.NearSquareRoot.CRTPositionClock
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontClock

/-! # Full native batch charge for the position program and the table-selected mask -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget
open DigitPacking Controlled.PositionProgram

noncomputable def nativeTick (ρ : ℝ) (n : ℕ) :=
  gridVolume n * (positionFactor ρ (addressBits n) + rowFactor (addressBits n) ρ + 1) + n

theorem le_gridVolume {n : ℕ} (hn : 2 ≤ n) : n ≤ gridVolume n :=
  (packed_volume hn).1.trans (Nat.mul_le_mul_left _ (by omega))

/-- The ceiling in both primitive rates and the fixed-`n` stage header fit
one address logarithm times the actual padded record volume. -/
theorem nativeTick_bound {ρ : ℝ} (hr : 0 ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ logs : ℕ, ∀ n, 2 ≤ n →
      (nativeTick ρ n:ℝ) ≤ C*gridVolume n*(1+(addressBits n:ℝ))^ρ*
        (1+Real.log (2+(addressBits n:ℝ)))^logs := by
  refine ⟨32,by norm_num,1,fun n hn => ?_⟩
  let k := addressBits n
  let V := gridVolume n
  let P := (1+(k:ℝ))^ρ
  let L := 1+Real.log (2+(k:ℝ))
  have volume : (n:ℝ) ≤ V := by exact_mod_cast le_gridVolume hn
  have oneL : 1 ≤ L := by
    unfold L
    linarith [Real.log_nonneg (show (1:ℝ) ≤ 2+k by linarith [Nat.cast_nonneg (α:=ℝ) k])]
  have log : 1+(Nat.clog 2 (k+1):ℝ) ≤ 4*L := by
    have := PhysicalWalshNode.FrontClock.clog_le k
    dsimp [L] at oneL ⊢
    linarith
  have Ppos : 0 ≤ P := by dsimp [P]; positivity
  have rate : positionRate ρ k = (1+(Nat.clog 2 (k+1):ℝ))*P := by
    unfold positionRate P
    push_cast
    rw [add_comm (k:ℝ) 1]
  have P_le : P ≤ positionRate ρ k := by
    rw [rate]
    exact le_mul_of_one_le_left Ppos (by simp)
  have row := row_factor_time k hr
  rw [add_comm (k:ℝ) 1] at row
  change (rowFactor k ρ:ℝ)+1 ≤ 4*P at row
  have price : (positionFactor ρ k:ℝ)+(rowFactor k ρ:ℝ)+1+1 ≤ 8*positionRate ρ k := by
    linarith only [positionFactor_time hr k,row,P_le]
  have both := mul_le_mul_of_nonneg_left price (Nat.cast_nonneg V)
  have logCost := mul_le_mul_of_nonneg_right log Ppos
  rw [←rate] at logCost
  have bound := mul_le_mul_of_nonneg_left logCost (show 0 ≤ 8*(V:ℝ) by positivity)
  change ((V*(positionFactor ρ k+rowFactor k ρ+1)+n:ℕ):ℝ) ≤ 32*(V:ℝ)*P*L^1
  push_cast
  rw [pow_one]
  calc
    _ ≤ (V:ℝ)*((positionFactor ρ k:ℝ)+(rowFactor k ρ:ℝ)+1+1) := by linarith
    _ ≤ (V:ℝ)*(8*positionRate ρ k) := both
    _ ≤ 32*(V:ℝ)*P*L := by linarith only [bound]

end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
