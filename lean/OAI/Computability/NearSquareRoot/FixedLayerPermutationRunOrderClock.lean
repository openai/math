import OAI.Computability.NearSquareRoot.FixedLayerPermutationTickClock

/-! # Same-exponent row clock for the effective Fourier batch schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedLayer
open Filter FixedCandidate DigitPacking SynchronizedPermutationBudget

/-- The schedule has this many passes at most, even in a padded final batch. -/
def permPassCount (N : ℕ) := (32*140^2)*(1+Nat.clog 2 (addressBits N+1))^2

/-- A complete row pays for one copy of the live array arena and every pass. -/
def permProfileClock (tick arena : ℕ → ℕ) (N : ℕ) :=
  arena N + permPassCount N*tick N

theorem permProfile_rate (tick arena : ℕ → ℕ) {N : ℕ} (valid : Directory N)
    (room : 8*SynchronizedPermutationBudget.width (addressBits N) ≤ addressBits N) :
    (order (addressBits N) ((box N).length/4)).length*tick N ≤ permProfileClock tick arena N :=
  (Nat.mul_le_mul_right _ (order_count (BoxFin.blockCount_le valid) room)).trans (Nat.le_add_left ..)

theorem permProfile_arena (tick arena : ℕ → ℕ) (N : ℕ) : arena N ≤ permProfileClock tick arena N :=
  Nat.le_add_right ..

private theorem count_bound (N : ℕ) :
    (permPassCount N : ℝ) ≤ (32*140^2*16)*(1+Real.log (2+(addressBits N:ℝ)))^2 := by
  let k := addressBits N
  let L := 1+Real.log (2+(k:ℝ))
  have h := PhysicalWalshNode.FrontClock.clog_le k
  have nonneg := Real.log_nonneg (show (1:ℝ) ≤ 2+k by linarith [Nat.cast_nonneg (α := ℝ) k])
  have upper : 1+(Nat.clog 2 (k+1):ℝ) ≤ 4*L := by dsimp only [L]; linarith
  have sq := pow_le_pow_left₀ (by positivity) upper 2
  change ((32*140^2*(1+Nat.clog 2 (k+1))^2 : ℕ):ℝ) ≤ (32*140^2*16)*L^2
  push_cast
  linarith only [sq]

/-- On sufficiently large good inputs the logarithmic number of passes is
absorbed by the logarithmic factor of the row clock, with the same exponent. -/
theorem permProfile_rowClock {η : ℝ} {tick arena : ℕ → ℕ} (hη : 0 ≤ η)
    (good : ∀ᶠ N in atTop, tick N = nativeTick η N ∧ arena N = N) :
    RowClock η (permProfileClock tick arena) := by
  have passes := (nativeTick_rowClock hη).mulCount (count := permPassCount) (D := 32*140^2*16)
    (by norm_num) 2 (Eventually.of_forall count_bound)
  obtain ⟨C,pos,l,est⟩ := (RowClock.linear hη).add passes
  refine ⟨C,pos,l,?_⟩
  filter_upwards [est,good] with N bound eq
  simpa only [permProfileClock,eq.1,eq.2,id_eq] using bound

end FixedLayer

end NearSquareRoot
end Computability
end OAI
