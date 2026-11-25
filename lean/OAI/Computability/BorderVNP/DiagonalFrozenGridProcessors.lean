import OAI.Computability.BorderVNP.DiagonalJointLength
import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts

/-! # One initial physical tile for every processor in the selected batch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Cover Packing Filter TeamScales Epoch PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {F : Type} [Field F] {e : PaidIdentity F D m} {S : SiteSchedule e}
    {a extra E degree Q A B j : ℕ} {s : EpochScales S a extra}

/-- The initial cover grows faster than its fixed single-level loss, so
after one common threshold the physical tile list covers the whole batch. -/
theorem JointSchedule.eventually_frozen_grid_processors (b : JointSchedule s E degree Q A B j) :
    ∀ᶠ n : ℕ in atTop, let r := stretch b.ρ n
      r ≤ ExternalSew.GridHosts.tileCount (Fintype.card (Cube D)) (CoverScale.initialDepth (Cube D) r n-1) := by
  filter_upwards [b.eventually_lengths 0,eventually_rpow_gap (by norm_num : (0:ℝ)<9/10) (CoverScale.factor (Cube D))]
    with n measured floor
  let r := stretch b.ρ n
  let start := CoverScale.initialDepth (Cube D) r n
  have positive : 0 < start := Nat.succ_pos _
  have tile : ExternalSew.GridHosts.tileCount (Fintype.card (Cube D)) (start-1) = CoverScale.sites (Cube D) start := by
    have h : start-1+2=start+1 := by omega
    simp only [ExternalSew.GridHosts.tileCount,CoverScale.sites,h,Fintype.card_fun,Fintype.card_fin]
  rw [Real.rpow_zero,mul_one] at floor
  have factorPos : (0:ℝ) < CoverScale.factor (Cube D) := by exact_mod_cast zero_lt_one.trans (CoverScale.one_lt_factor _)
  have lower : (r:ℝ) ≤ (CoverScale.sites (Cube D) start : ℝ) :=
    ((le_div_iff₀ factorPos).mpr (mul_le_mul_of_nonneg_left floor (by positivity))).trans measured.cover.2.2.1.le
  change r ≤ ExternalSew.GridHosts.tileCount _ (start-1)
  rw [tile]
  exact_mod_cast lower

end Diagonal

end BorderVNP
end Computability
end OAI
