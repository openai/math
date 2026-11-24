import OAI.Computability.VPVNP.CompressionParameters
import OAI.Computability.VPVNP.RAMSiteBounds

/-!
# Integer computations of the transcript parameters

The prescribed rational multiples of the binary logarithm can be rounded
using only integer powers and integer logarithms. In particular a processor
need not compute any real-valued function to determine its field widths.
The virtual site count is the least power of two satisfying the budget
inequality of Section 11.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

/-- Ceiling of a nonnegative rational multiple of `log₂ n` computed over
integers. For fixed numerator and positive denominator the powers have
`O(log n)` bits. -/
def roundedUp (p q n : ℕ) : ℕ := Nat.clog (2^q) (n^p)

/-- Floor used for the number of compression blocks. -/
def roundedDown (p q n : ℕ) : ℕ := Nat.log (2^q) (n^p)

private theorem scaled_log (p q n : ℕ) :
    Real.logb ((2^q : ℕ) : ℝ) ((n^p : ℕ) : ℝ) = ((p:ℝ)/q) * Real.logb 2 n := by
  push_cast
  simp only [Real.logb, Real.log_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem roundedUp_eq (p q n : ℕ) :
    roundedUp p q n = Compression.bucketExponent ((p:ℝ)/q) n := by
  rw [roundedUp, Compression.bucketExponent, ← Real.natCeil_logb_natCast, scaled_log]

theorem roundedDown_eq (p q n : ℕ) :
    roundedDown p q n = Compression.blockCount ((p:ℝ)/q) n := by
  rw [roundedDown, Compression.blockCount, ← Real.natFloor_logb_natCast, scaled_log]

/-- The rounding of the live address width from §9.1. -/
def addressWidth (B n : ℕ) : ℕ := B * Nat.clog 2 n

theorem clog_le_log2_succ (n : ℕ) : Nat.clog 2 n ≤ n.log2 + 1 := by
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  cases n with
  | zero => simp
  | succ n => exact ((Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)).le

theorem log2_le_addressWidth {B : ℕ} (hB : 1 ≤ B) (n : ℕ) : n.log2 ≤ addressWidth B n := by
  rw [Nat.log2_eq_log_two]
  exact (Nat.log_le_clog 2 n).trans (Nat.le_mul_of_pos_left _ hB)

/-- Binary site count for the virtual group in §11. -/
def virtualSiteExponent (r n : ℕ) : ℕ :=
  Nat.clog 2 (2^r * n * Nat.clog 2 n) - roundedUp 1 4 n

/-- The chosen number of virtual sites is exactly the least permitted power of
two, including cases in which a single bucket covers the entire budget. -/
theorem virtualSiteExponent_le_iff (r n d : ℕ) :
    virtualSiteExponent r n ≤ d ↔ 2^r * n * Nat.clog 2 n ≤ 2^d * 2^(roundedUp 1 4 n) := by
  rw [virtualSiteExponent, Nat.sub_le_iff_le_add, Nat.clog_le_iff_le_pow (by decide : 1 < 2), pow_add]

/-- For the actual live choices of Section 9, the whole literal and shared
input is available to the coefficient program at every sufficiently large
length. -/
theorem eventually_liveInputFits (program : UniversalMachine.Program) (B : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ProcessorInput.Fits program n (addressWidth B n) (Compression.liveBucket δ n)
        ((addressWidth B n + 10)^4) := by
  filter_upwards [eventually_processorInputFits program B hδ, Filter.eventually_ge_atTop 1] with n h hn
  apply h (addressWidth B n) (Compression.bucketExponent (1-δ) n)
  · exact Nat.mul_le_mul_left _ (clog_le_log2_succ _)
  · simpa [Compression.liveBucket] using (Compression.liveBucket_bounds hδ' hn).2

end BurstRAM

end VPVNP
end Computability
end OAI
