import OAI.Computability.NearSquareRoot.PhysicalWalshPositionRate
import OAI.Computability.NearSquareRoot.CRTPositionClock

/-! # Native bit-cloth volume and the selected Walsh clock -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open FixedPoint Controlled.PositionProgram

/-- Each addressed record carries one signed real and one signed imaginary component. -/
def nativeVolume (k : ℕ) := 2^k * (2*(componentBits k+1))

theorem native_volume_bound (k : ℕ) : nativeVolume k ≤ 192*Odd.volume k := by
  unfold nativeVolume Odd.volume componentBits
  rw [Nat.mul_left_comm 192]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem native_clock {ρ : ℝ} (hr : 0 ≤ ρ) (k : ℕ) :
    (nativeVolume k : ℝ)*((positionFactor ρ k : ℝ)+1) ≤ 768*(Odd.time k:ℝ)*(1+(k:ℝ))^ρ := by
  have v : (nativeVolume k : ℝ) ≤ 192*(Odd.volume k:ℝ) := by exact_mod_cast native_volume_bound k
  have rate := mul_le_mul v (positionFactor_time hr k) (by positivity) (by positivity)
  apply rate.trans_eq
  unfold Odd.time Odd.volume GridTask.recordCost positionRate
  push_cast
  rw [add_comm (k:ℝ) 1]
  ring

/-- The native router and the two conversion scans satisfy the sparse time and
space estimates uniformly over address widths, including width zero. -/
theorem native_sparse_bounds {ρ : ℝ} (hr : 0 ≤ ρ) : ∃ B : ℕ, ∀ k,
    nativeVolume k*(positionFactor ρ k+1)+Odd.volume k+1 ≤ B*(Pieces.sparseTime ρ k+1) ∧
    nativeVolume k+Odd.volume k+1 ≤ B*(Pieces.sparseSpace k+1) := by
  obtain ⟨D,time⟩ := position_time_bound hr 0
  refine ⟨768*D+387,fun k => ?_⟩
  have t := native_clock hr k
  have pay := time k
  rw [pow_zero] at pay
  have time' : (nativeVolume k*(positionFactor ρ k+1):ℕ) ≤ (768*D)*(Pieces.sparseTime ρ k+1) := by
    have h : (nativeVolume k : ℝ)*((positionFactor ρ k:ℝ)+1) ≤ (768*D:ℕ)*(Pieces.sparseTime ρ k+1:ℕ) := by
      push_cast at pay ⊢
      linarith only [pay,t]
    exact_mod_cast h
  have space := Pieces.odd_volume_le k
  have clock := Pieces.space_le_clock hr k
  have n := native_volume_bound k
  rw [Nat.add_mul,Nat.add_mul]
  constructor <;> omega

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
