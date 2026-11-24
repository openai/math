import OAI.Computability.VPVNP.CompressorRecordsCursorWords
import OAI.Computability.VPVNP.CompressorRecordsCursorScan
import OAI.Computability.VPVNP.CursorCompressionBudget
import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.RAMWordBounds

/-!
# Word space for initializing the cursor records

At fixed degree, the number of rows is polynomial in the input length and
independent of where the physical address is split into base and lane blocks.
The same word accommodates the initial width, the six arrays and a timestamp
for every probe of the scan. A polynomially bounded starting offset can be
chosen before the eventual length threshold.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.CursorRAM

open CursorBounds Filter

/-- Splitting the virtual address does not change the number of actual ports. -/
theorem rowCount_eq_positions {B n b l : ℕ} (h : b+l = virtualBits B n) (a : ℕ) :
    rowCount b l a = initialPositions B n * 2^a := by
  unfold rowCount initialPositions
  rw [← h, pow_add]
  ac_rfl

/-- The number of actual cursor positions is polynomially bounded for fixed address exponent. -/
theorem bounded_positions (B : ℕ) : PolynomiallyBounded (initialPositions B) := by
  let upper := ((PolynomiallyBounded.const 2).mul PolynomiallyBounded.id).pow (B+2)
  refine (upper.mul upper).of_eventually_le 1 fun n hn ↦ ?_
  have hlog : 2 ^ n.log2 ≤ n := (Nat.le_log2 (by omega : n ≠ 0)).mp le_rfl
  have hc : 2 ^ Nat.clog 2 n ≤ 2*n := calc
    _ ≤ 2 ^ (n.log2 + 1) := Nat.pow_le_pow_right Nat.zero_lt_two (BurstRAM.clog_le_log2_succ n)
    _ = 2 * 2 ^ n.log2 := pow_succ' ..
    _ ≤ _ := Nat.mul_le_mul_left _ hlog
  have hv : 2 ^ virtualBits B n ≤ (2*n) ^ (B+2) := calc
    _ ≤ 2 ^ ((B+2)*Nat.clog 2 n) := Nat.pow_le_pow_right Nat.zero_lt_two (virtualBits_le B n)
    _ = (2 ^ Nat.clog 2 n) ^ (B+2) := by rw [Nat.mul_comm, pow_mul]
    _ ≤ _ := Nat.pow_le_pow_left hc _
  exact Nat.mul_le_mul hv (Nat.lt_two_pow_self.le.trans hv)

/-- A fixed polynomially bounded natural address fits strictly below the word modulus. -/
theorem eventual_word_room (B : ℕ) (hB : 1 ≤ B) {f : ℕ → ℕ}
    (hf : PolynomiallyBounded f) : ∀ᶠ n : ℕ in atTop, f n < 2 ^ wordBits B n := by
  obtain ⟨A,d,N,h⟩ := hf
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop A,
    BurstRAM.eventually_polynomial_lt_wordModulus (d+1)] with n hn hA hp
  apply lt_of_le_of_lt ((h n hn).trans (Nat.mul_le_mul_right (n^d) hA))
  rw [← pow_succ']
  exact hp (addressBits B n) (BurstRAM.log2_le_addressWidth hB n)

private theorem eventual_width (B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, initialWidth B n < 2 ^ wordBits B n := by
  have ha := Compression.eventually_absorb_polylog
    (56 * ((B : ℝ) + 3)^2 * ((B : ℝ) + 10)^4) 6
    (show (1/4 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [ha, eventually_ge_atTop 2, eventual_word_room B hB PolynomiallyBounded.id]
    with n habs hn hword
  have hw : (initialWidth B n : ℝ) ≤ n := (initialWidth_bound B n hn).trans (by simpa using habs)
  exact (show initialWidth B n ≤ n by exact_mod_cast hw).trans_lt hword

/-- All capacity conditions for the first descriptor scan. Seven words of
cost per row account for one call and its six probes. The threshold works
for every split of the virtual address at each sufficiently large length. -/
theorem eventually_cursorCapacity (B a : ℕ) (hB : 1 ≤ B) {start : ℕ → ℕ}
    (hs : PolynomiallyBounded start) :
    ∀ᶠ n : ℕ in atTop, ∀ b l, b+l = virtualBits B n →
      1 < b+l ∧ start n + 6*rowCount b l a ≤ 2 ^ wordBits B n ∧
      initialWidth B n < 2 ^ wordBits B n ∧ start n + 7*rowCount b l a ≤ 2 ^ wordBits B n := by
  have hrows := (bounded_positions B).mul (PolynomiallyBounded.const (2^a))
  have hcost := hs.add ((PolynomiallyBounded.const 7).mul hrows)
  filter_upwards [eventually_ge_atTop 3, eventual_word_room B hB hcost, eventual_width B hB]
    with n hn hroom hwidth
  intro b l he
  have hc : 1 < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (by omega)
  have hd := (hc.trans_le (Nat.le_mul_of_pos_left _ hB)).trans_le (addressBits_le_virtualBits B n hn)
  change start n + 7 * (initialPositions B n * 2^a) < 2 ^ wordBits B n at hroom
  rw [← rowCount_eq_positions he] at hroom
  exact ⟨he ▸ hd, by omega, hwidth, hroom.le⟩

/-- Every chronological RAM record of the native scan has a word-sized
address, timestamp and ordinal as soon as the scan's ending cost fits. -/
theorem scan_probeRecords_fitsWord {w start k n : ℕ} (p : Fin 11 → BurstRAM.Word w)
    (room : start + 7*n ≤ 2^w) {r : RAMMemory.Record (BurstRAM.Word w)}
    (hr : r ∈ BurstRAM.probeRecords start (scanReports p k n)) : BurstRAM.RecordFitsWord r := by
  apply BurstRAM.probeRecords_fitsWord _ hr
  change start + RAMBuckets.cost (fun r : BurstRAM.Report w ↦ BurstRAM.countProbes r.events)
    (scanReports p k n) ≤ 2^w
  rwa [scan_cost]

end CompressorRecords.CursorRAM

end VPVNP
end Computability
end OAI
