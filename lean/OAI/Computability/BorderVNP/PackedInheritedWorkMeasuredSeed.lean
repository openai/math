import OAI.Computability.BorderVNP.PackedInheritedWorkSeedFrame
import OAI.Computability.BorderVNP.PackedInheritedWorkSeedCost

/-! # Rectangular gate bound at the width-bearing grouped seed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.PublicCapacity
open Packing Packing.Inherited.WorkWords SelectedSchedule Diagonal TeamScales Filter
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)
    {n r d T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
    {σ : Type} [Fintype σ]

/-- Every two-gate geometric initializer of the actual grouped seed pays for its two full
width passes and leaf guard within the bottom rectangle. -/
theorem seedWidthFrame_rowWork
    (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*logWidth r n) 0)) (small : base.size ≤ 2)
    (edgeFit : (boundary S (d+1) 0).edges ≤ 2^(60*logWidth r n)) (hL : 1 ≤ logWidth r n) :
    (seedWidthFrame S plan base).size+1 ≤ rowWork (3+64000*66^3) (CoverScale.sites (Cube D) (d+1))
      (logWidth r n) 3 (bottom (D:=D) (d+1)) := by
  unfold seedWidthFrame
  apply BottomPrep.frame_rowWork _ _ _ _ _ _ _ _ _ _ small _ edgeFit rfl hL
  rw [gridShape_zero]
  exact le_rfl

/-- The cable range in the initial width computation follows uniformly from the calibrated
cover. Thus the cubic leaf bound holds for every realized seed plan at the chosen depth. -/
theorem eventually_seedWidthFrame_rowWork {a x : ℕ} (scales : EpochScales S a x) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let d := CoverScale.initialDepth (Cube D) r n-1
      let L := logWidth r n
      ∀ {T copies headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
        {σ : Type} [Fintype σ] (base : Frame σ (Pins S (d+1) (boundary S (d+1)) (60*L) 0)),
        base.size ≤ 2 → (seedWidthFrame S plan base).size+1 ≤
          rowWork (3+64000*66^3) (CoverScale.sites (Cube D) (d+1)) L 3 (bottom (D:=D) (d+1)) := by
  filter_upwards [eventually_boundaries S scales,eventually_ge_atTop 1] with n rows hn
  intro r hr d L T copies headerFactor Q plan σ _ base small
  have hs : 1 ≤ CoverScale.initialDepth (Cube D) r n := Nat.succ_pos _
  have depth : d+1 = CoverScale.initialDepth (Cube D) r n := by dsimp only [d]; omega
  let start := CoverScale.initialDepth (Cube D) r n
  have hL : 1 ≤ L := by
    rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1≤Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  have fit : r*n ≤ 2^(60*L) := by
    have pow : 2*n*r ≤ 2^L := by
      rw [show L = Nat.clog 2 (2*n*r) from public_logWidth n r]
      exact Nat.le_pow_clog (by decide) _
    exact (show r*n ≤ 2*n*r by nlinarith).trans (pow.trans (Nat.pow_le_pow_right (by decide) (by omega)))
  apply seedWidthFrame_rowWork S plan base small _ hL
  rw [depth]
  exact (show (boundary S start 0).edges ≤ (boundary S start 0).volume (CoverScale.sites (Cube D) start)
    by dsimp only [Shape.volume]; omega).trans (((rows r hr).1 0 (Nat.zero_le _)).trans fit)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
