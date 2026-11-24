import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rounded compression and bucket exponents

Section 9.1 of *VP and VNP differ over every field* chooses the number of
compressor blocks and the sizes of the live and virtual transcript buckets
by rounding multiples of the binary logarithm of the input length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

/-- Number of compressor blocks used in §12. -/
noncomputable def blockCount (θ : ℝ) (n : ℕ) : ℕ := ⌊θ * Real.logb 2 n⌋₊

/-- Binary exponent of a transcript bucket. -/
noncomputable def bucketExponent (x : ℝ) (n : ℕ) : ℕ := ⌈x * Real.logb 2 n⌉₊

/-- The live group uses buckets of size `K`. -/
noncomputable def liveBucket (δ : ℝ) (n : ℕ) : ℕ := 2 ^ bucketExponent (1 - δ) n

/-- The virtual network uses buckets of size `K′`. -/
noncomputable def virtualBucket (n : ℕ) : ℕ := 2 ^ bucketExponent (1 / 4) n

/-- Comparing a rounded-down rational exponent requires only an integer power comparison. -/
theorem le_blockCount_ratio_iff {a b n k : ℕ} (hb : 0 < b) (hn : 1 ≤ n) :
    k ≤ blockCount ((a : ℝ) / b) n ↔ 2 ^ (k * b) ≤ n ^ a := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) ^ a := pow_pos (zero_lt_one.trans_le hn') _
  have hlog := Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn'
  rw [blockCount, Nat.le_floor_iff (mul_nonneg (by positivity) hlog), div_mul_eq_mul_div,
    le_div_iff₀ hb', ← Real.logb_pow, ← Nat.cast_mul,
    Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_natCast]
  norm_cast

/-- Comparing a rounded-up rational exponent requires only an integer power comparison. -/
theorem bucketExponent_ratio_le_iff {a b n k : ℕ} (hb : 0 < b) (hn : 1 ≤ n) :
    bucketExponent ((a : ℝ) / b) n ≤ k ↔ n ^ a ≤ 2 ^ (k * b) := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) ^ a := pow_pos (zero_lt_one.trans_le hn') _
  rw [bucketExponent, Nat.ceil_le, div_mul_eq_mul_div, div_le_iff₀ hb',
    ← Real.logb_pow, ← Nat.cast_mul, Real.logb_le_iff_le_rpow (by norm_num) hpos,
    Real.rpow_natCast]
  norm_cast

/-- An executable integer formula for the number of compressor blocks. -/
theorem blockCount_ratio_eq {a b n : ℕ} (hb : 0 < b) (hn : 1 ≤ n) :
    blockCount ((a : ℝ) / b) n = Nat.log 2 (n ^ a) / b := by
  apply eq_of_forall_le_iff
  intro k
  rw [le_blockCount_ratio_iff hb hn, Nat.le_div_iff_mul_le hb,
    Nat.le_log_iff_pow_le Nat.one_lt_two (pow_ne_zero _ (by omega))]

/-- An executable integer formula for the binary exponent of a transcript bucket. -/
theorem bucketExponent_ratio_eq {a b n : ℕ} (hb : 0 < b) (hn : 1 ≤ n) :
    bucketExponent ((a : ℝ) / b) n = (Nat.clog 2 (n ^ a) + b - 1) / b := by
  apply eq_of_forall_ge_iff
  intro k
  rw [bucketExponent_ratio_le_iff hb hn, ← Nat.ceilDiv_eq_add_pred_div,
    ceilDiv_le_iff_le_mul hb, Nat.clog_le_iff_le_pow Nat.one_lt_two, Nat.mul_comm b k]

private theorem two_rpow_mul_logb (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (2 : ℝ) ^ (x * Real.logb 2 y) = y ^ x := by
  rw [mul_comm, Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
    Real.rpow_logb (by norm_num) (by norm_num) hy]

/-- Rounding a nonnegative bucket exponent upwards costs at most a factor of two. -/
theorem bucketExponent_bounds {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : 1 ≤ n) :
    (n : ℝ) ^ x ≤ (2 : ℝ) ^ bucketExponent x n ∧
      (2 : ℝ) ^ bucketExponent x n ≤ 2 * (n : ℝ) ^ x := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := zero_lt_one.trans_le hn'
  have hnonneg := mul_nonneg hx (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn')
  rw [← two_rpow_mul_logb x hnpos, bucketExponent, ← Real.rpow_natCast]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  · calc
      _ ≤ (2 : ℝ) ^ (x * Real.logb 2 n + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.ceil_lt_add_one hnonneg).le
      _ = _ := by rw [Real.rpow_add_one (by norm_num), mul_comm]

theorem liveBucket_bounds {δ : ℝ} {n : ℕ} (hδ : δ ≤ 1) (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 - δ) ≤ (liveBucket δ n : ℝ) ∧
      (liveBucket δ n : ℝ) ≤ 2 * (n : ℝ) ^ (1 - δ) := by
  simpa [liveBucket] using bucketExponent_bounds (sub_nonneg.mpr hδ) hn

theorem virtualBucket_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 / 4 : ℝ) ≤ (virtualBucket n : ℝ) ∧
      (virtualBucket n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  simpa [virtualBucket] using bucketExponent_bounds (by norm_num : 0 ≤ (1 / 4 : ℝ)) hn

/-- Rounding the number of blocks down costs at most a factor of two in
the compression estimate. -/
theorem inv_two_pow_blockCount (θ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    1 / (2 : ℝ) ^ blockCount θ n ≤ 2 * (n : ℝ) ^ (-θ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfloor := (Nat.lt_floor_add_one (θ * Real.logb 2 n)).le
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2 : ℝ)) hfloor
  rw [two_rpow_mul_logb θ hn', Real.rpow_add_one (by norm_num), Real.rpow_natCast] at h
  rw [Real.rpow_neg hn'.le, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity)
    (Real.rpow_pos_of_pos hn' θ), one_mul, mul_comm]
  exact h

/-- The growth of histories through all blocks fits the power slack fixed in §9.1. -/
theorem history_pow_blockCount_le {C₂ θ : ℝ} {n : ℕ} (hC : 1 ≤ C₂) (hθ : 0 ≤ θ)
    (hn : 1 ≤ n) (hexp : θ * Real.logb 2 C₂ ≤ 1 / 100) :
    C₂ ^ blockCount θ n ≤ (n : ℝ) ^ (1 / 100 : ℝ) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos := zero_lt_one.trans_le hn'
  have hnonneg := mul_nonneg hθ (Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn')
  rw [blockCount, ← Real.rpow_natCast]
  calc
    _ ≤ C₂ ^ (θ * Real.logb 2 n) := Real.rpow_le_rpow_of_exponent_le hC (Nat.floor_le hnonneg)
    _ = (2 : ℝ) ^ (Real.logb 2 C₂ * (θ * Real.logb 2 n)) := by
      rw [Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ)),
        Real.rpow_logb (by norm_num) (by norm_num) (zero_lt_one.trans_le hC)]
    _ = (n : ℝ) ^ (θ * Real.logb 2 C₂) := by
      rw [mul_left_comm, ← mul_assoc, two_rpow_mul_logb _ hnpos]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' hexp

/-- The rational exponents of §9.1 can be chosen for every fixed per-block
growth constant from Theorem 7.1. -/
theorem exists_compression_exponents (C₂ : ℝ) (hC : 1 ≤ C₂) :
    ∃ θ δ : ℚ, 0 < θ ∧ θ < 1 / 100 ∧ 0 < δ ∧ δ < θ / 10 ∧
      (θ : ℝ) * Real.logb 2 C₂ ≤ 1 / 100 := by
  have hlog := Real.logb_nonneg (b := 2) (by norm_num) hC
  have hpos : 0 < 1 + Real.logb 2 C₂ := by linarith
  have hb : 0 < min (1 / 100 : ℝ) ((1 / 100) / (1 + Real.logb 2 C₂)) :=
    lt_min (by norm_num) (div_pos (by norm_num) hpos)
  obtain ⟨θ, hθ, hθb⟩ := exists_rat_btwn hb
  obtain ⟨hsmall, hbudget⟩ := lt_min_iff.mp hθb
  have hθq : 0 < θ := Rat.cast_pos.mp hθ
  refine ⟨θ, θ / 20, hθq, ?_, div_pos hθq (by norm_num), ?_, ?_⟩
  · apply (Rat.cast_lt (K := ℝ)).mp
    simpa using hsmall
  · linarith
  · have hprod := (lt_div_iff₀ hpos).mp hbudget
    linarith

/-- The same fixed pair of rationals gives the required history bound at
every positive input length. -/
theorem exists_compression_budgets (C₂ : ℝ) (hC : 1 ≤ C₂) :
    ∃ θ δ : ℚ, 0 < θ ∧ θ < 1 / 100 ∧ 0 < δ ∧ δ < θ / 10 ∧
      ∀ n : ℕ, 1 ≤ n → C₂ ^ blockCount (θ : ℝ) n ≤ (n : ℝ) ^ (1 / 100 : ℝ) := by
  obtain ⟨θ, δ, hθ, hθ', hδ, hδ', hlog⟩ := exists_compression_exponents C₂ hC
  exact ⟨θ, δ, hθ, hθ', hδ, hδ', fun _ hn =>
    history_pow_blockCount_le hC (Rat.cast_nonneg.mpr hθ.le) hn hlog⟩

/-- Every positive choice of the block exponent yields arbitrarily many blocks
at sufficiently large input lengths. -/
theorem tendsto_blockCount {θ : ℝ} (hθ : 0 < θ) :
    Filter.Tendsto (blockCount θ) Filter.atTop Filter.atTop :=
  tendsto_nat_floor_atTop.comp (Filter.Tendsto.const_mul_atTop hθ
    ((Real.tendsto_logb_atTop (by norm_num : 1 < (2 : ℝ))).comp tendsto_natCast_atTop_atTop))

/-- An address multiplier at least the rounded lane demand per binary
logarithm supplies all lane bits required by the compressor blocks. -/
theorem laneBits_le_addressWidth {θ : ℝ} {b₀ B n : ℕ} (hθ : 0 ≤ θ) (hn : 1 ≤ n)
    (hB : ⌈(b₀ : ℝ) * θ⌉₊ ≤ B) :
    b₀ * blockCount θ n ≤ B * Nat.clog 2 n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog := Real.logb_nonneg (by norm_num : 1 < (2 : ℝ)) hn'
  have hB' : (b₀ : ℝ) * θ ≤ B := (Nat.le_ceil _).trans (by exact_mod_cast hB)
  have hclog : Real.logb 2 n ≤ (Nat.clog 2 n : ℝ) := by
    rw [← Real.natCeil_logb_natCast 2 n]
    exact Nat.le_ceil _
  have hfloor : (blockCount θ n : ℝ) ≤ θ * Real.logb 2 n := Nat.floor_le (mul_nonneg hθ hlog)
  have h : (b₀ : ℝ) * (blockCount θ n : ℝ) ≤ (B : ℝ) * (Nat.clog 2 n : ℝ) := calc
    _ ≤ (b₀ : ℝ) * (θ * Real.logb 2 n) := mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
    _ = ((b₀ : ℝ) * θ) * Real.logb 2 n := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul hB' hclog hlog (Nat.cast_nonneg _)
  exact_mod_cast h

/-- Choosing the multiplier of the address width at least five ensures the
processor count dominates the fifth power used in the counter budget. -/
theorem pow_five_le_processorCount (n : ℕ) {B : ℕ} (hB : 5 ≤ B) :
    n ^ 5 ≤ 2 ^ (B * Nat.clog 2 n) := by
  calc
    n ^ 5 ≤ (2 ^ Nat.clog 2 n) ^ 5 := Nat.pow_le_pow_left (Nat.le_pow_clog Nat.one_lt_two n) _
    _ = 2 ^ (5 * Nat.clog 2 n) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hB)

end Compression

end VPVNP
end Computability
end OAI
