import OAI.Computability.VPVNP.CursorBounds

/-!
# Capacity of the primed coefficient-counting RAM

The virtual bucket definition includes one growing factor of the rounded
binary logarithm. It absorbs any fixed constant in the two site scans and
the preorder traversal, including a single comparison against the nominated
histogram. The same choice leaves space in every two-address-width counter
for all productions emitted by the pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open Filter CursorBounds Compression

/-- A virtual bucket eventually covers any fixed number of external probes
plus the startup charge. -/
theorem eventually_virtualBucket_ge (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K ≤ 2^(roundedUp 1 4 n) := by
  filter_upwards [eventually_ge_atTop (K^4)] with n hn
  have hp := Nat.le_pow_clog (by decide : 1 < 2^4) (n^1)
  have h : n ≤ (2^(roundedUp 1 4 n))^4 := by
    change n ≤ (2^(Nat.clog (2^4) (n^1)))^4
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simpa using hp
  exact (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp (hn.trans h)

/-- `O(Rn)` total probes and the final length-`t` histogram comparison
fit the exact budget `R′K′`. The coefficient on the right of the work
estimate is a fixed program constant. -/
theorem eventually_pairExternalBudget (B K : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ t, t ≤ processorCount B n →
      K * (processorCount B n * n + t + 1) ≤
        2^(virtualBits B n) * 2^(roundedUp 1 4 n) := by
  filter_upwards [eventually_ge_atTop (2^(3*K)), eventually_ge_atTop 1] with n hn hn' t ht
  let R := processorCount B n
  have hR : 1 ≤ R := Nat.two_pow_pos _
  have hlog : 3*K ≤ Nat.clog 2 n := by
    have hf := (Nat.le_log2 (by omega : n ≠ 0)).mpr hn
    rw [Nat.log2_eq_log_two] at hf
    exact hf.trans (Nat.log_le_clog ..)
  have hcap := (virtualSiteExponent_le_iff (addressWidth B n) n (virtualBits B n)).mp le_rfl
  have hRn : R ≤ R*n := Nat.le_mul_of_pos_right _ hn'
  calc
    K*(R*n+t+1) ≤ K*(3*(R*n)) := by apply Nat.mul_le_mul_left; change t ≤ R at ht; omega
    _ = (R*n)*(3*K) := by ac_rfl
    _ ≤ R*n*Nat.clog 2 n := Nat.mul_le_mul_left _ hlog
    _ ≤ _ := hcap

/-- The full collection of `2R` trees of `n` leaves uses fewer than
`2^(2r)` labels, so every individual counter and each intermediate counter
fits in the advertised two-address-width field. -/
theorem pairLabels_lt {B n : ℕ} (hB : 2 ≤ B) (hn : 5 ≤ n) :
    2 * processorCount B n * (2*n-1) < 2^(2 * addressWidth B n) := by
  let R := processorCount B n
  have hs : n^2 ≤ R := by
    have hb := Nat.le_pow_clog (by decide : 1 < 2) n
    calc
      _ ≤ (2^(Nat.clog 2 n))^2 := Nat.pow_le_pow_left hb _
      _ = 2^(2 * Nat.clog 2 n) := by rw [← pow_mul, Nat.mul_comm]
      _ ≤ R := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hB)
  have hsmall : 2*(2*n-1) < R := by
    have h5 : 5*n ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ hn
    omega
  rw [show 2 * addressWidth B n = addressWidth B n + addressWidth B n by omega, pow_add]
  change 2*R*(2*n-1) < R*R
  rw [show 2*R*(2*n-1) = R*(2*(2*n-1)) by ac_rfl]
  exact Nat.mul_lt_mul_of_pos_left hsmall (Nat.two_pow_pos _)

end BurstRAM

end VPVNP
end Computability
end OAI
