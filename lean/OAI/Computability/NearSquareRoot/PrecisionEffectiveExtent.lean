import OAI.Computability.NearSquareRoot.PhysicalWalshPieceBudget
import OAI.Computability.NearSquareRoot.PhysicalWalshPaddingSetup

/-! # Pointwise padding bounds from the selected and spectator bit counts -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace WalshPadding

theorem depth_le_log {A k s : ℕ} (hA : 2 ≤ A) (hk : 1 ≤ k) (hs : s ≤ k) :
    depth A s ≤ Nat.log 2 k := by
  have h : 2^(Nat.log A k) ≤ k :=
    (Nat.pow_le_pow_left hA _).trans (Nat.pow_log_le_self _ (by omega))
  exact (Nat.log_mono_right ((Nat.div_le_self s 2).trans hs)).trans (Nat.le_log_of_pow_le (by decide) h)

theorem batchModulus_le_pow_log {A k s : ℕ} (hA : 2 ≤ A) (hk : 1 ≤ k) (hs : s ≤ k) (W : ℕ) :
    W^(depth A s) ≤ 2^(Nat.log 2 k * W) := by
  calc
    W^(depth A s) ≤ (2^W)^(depth A s) := Nat.pow_le_pow_left W.lt_two_pow_self.le _
    _ = 2^(depth A s*W) := by rw [← pow_mul, mul_comm W]
    _ ≤ 2^(Nat.log 2 k*W) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right W (depth_le_log hA hk hs))

theorem batchModulus_le_of_budget {A W k s : ℕ} (hA : 2 ≤ A) (hk : 1 ≤ k) (hs : s ≤ k)
    (room : Nat.log 2 k * W ≤ k-s) : W^(depth A s) ≤ 2^(k-s) :=
  (batchModulus_le_pow_log hA hk hs W).trans (Nat.pow_le_pow_right (by decide) room)

end WalshPadding

namespace PhysicalWalsh.Pieces

/-- The padded record tape is at most twice the original tape when there
are enough spectator bits for the largest recursive batch. -/
theorem extent_le_of_budget {A W k s : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (hs : s ≤ k) (room : Nat.log 2 k * W ≤ k-s) : extent A W k s ≤ 2*2^k := by
  have hrows := WalshPadding.paddedRows_le_double hW (WalshPadding.batchModulus_le_of_budget hA hk hs room)
  calc
    extent A W k s ≤ (2*2^(k-s))*2^s := Nat.mul_le_mul_right _ hrows
    _ = 2*2^k := by rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hs]

theorem extent_le_of_half {A W k s : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (half : 2*s ≤ k) (budget : (Nat.log 2 k+1)*W ≤ k/2) :
    extent A W k s ≤ 2*2^k := by
  apply extent_le_of_budget hA hW hk (by omega)
  rw [Nat.add_mul, one_mul] at budget
  omega

/-- A bound valid even with no spectator bits. The numerator may be padded
to a whole recursive batch, whose size is bounded separately. -/
theorem extent_le_of_log_budget {A W k s : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (hs : s ≤ k) (budget : Nat.log 2 k * W ≤ k) : extent A W k s ≤ 2^(2*k) := by
  let q := 2^(k-s)
  let M := W^WalshPadding.depth A s
  have hp : 0 < M := Nat.pow_pos hW
  have hm : M ≤ 2^k := (WalshPadding.batchModulus_le_pow_log hA hk hs W).trans
    (Nat.pow_le_pow_right (by decide) budget)
  have hceil : q ⌈/⌉ M ≤ q := (ceilDiv_le_iff_le_mul hp).mpr (Nat.le_mul_of_pos_left _ hp)
  calc
    extent A W k s ≤ (M*q)*2^s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left M hceil)
    _ = M*2^k := by rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hs]
    _ ≤ 2^k*2^k := Nat.mul_le_mul_right _ hm
    _ = 2^(2*k) := by rw [← pow_add,two_mul]

theorem extent_le_of_half_budget {A W k s : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (hs : s ≤ k) (budget : (Nat.log 2 k+1)*W ≤ k/2) : extent A W k s ≤ 2^(2*k) := by
  apply extent_le_of_log_budget hA hW hk hs
  rw [Nat.add_mul, one_mul] at budget
  omega

/-- Maximum number of appended records, in the same units as the input tape. -/
theorem extra_le_of_budget {A W k s : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (hs : s ≤ k) (room : Nat.log 2 k * W ≤ k-s) : PaddingHeader.extra A W k s ≤ 2^k := by
  have h := extent_le_of_budget hA hW hk hs room
  change WalshPadding.paddedRows (2^(k-s)) W (WalshPadding.depth A s)*2^s ≤ _ at h
  rw [← Padding.total A hW hs] at h
  omega

theorem sweepVolume_le_of_budget {A W k s w : ℕ} (hA : 2 ≤ A) (hW : 0 < W) (hk : 1 ≤ k)
    (hs : s ≤ k) (room : Nat.log 2 k * W ≤ k-s) :
    sweepVolume A W k s w ≤ (2*(2:ℝ)^k)*(w+1) := by
  unfold sweepVolume
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast extent_le_of_budget hA hW hk hs room) (by positivity)

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
