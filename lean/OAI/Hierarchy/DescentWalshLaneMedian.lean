import OAI.Hierarchy.DescentPackedWalshLanes
import Mathlib.Tactic

namespace OAI
/-! # Occupancy of the physical power-of-two packed Walsh word -/
namespace Hierarchy.DescentWalshDyadicBudget
open DescentPackedWalsh

theorem laneBits_median (m h p : ℕ) (nonzero : 0<p) :
    2^(laneBits m h p)=2^m ∨ h≤16*p*2^(laneBits m h p) := by
  unfold laneBits
  rcases le_total m (Nat.log 2 (h/(8*p))) with first|last
  · exact Or.inl (by rw [min_eq_left first])
  · right
    rw [min_eq_right last]
    have raw:=Nat.lt_pow_succ_log_self (by decide : 1<2) (h/(8*p))
    rw [pow_succ] at raw
    have rate : h<(2^Nat.log 2 (h/(8*p))*2)*(8*p) := (Nat.div_lt_iff_lt_mul (by omega)).mp raw
    nlinarith only [rate]

end Hierarchy.DescentWalshDyadicBudget

end OAI
