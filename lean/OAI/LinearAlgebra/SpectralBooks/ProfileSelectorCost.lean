import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Rounding the binary selector width in a network shortening

A strict saving with fractional selector cost persists after taking a sufficiently large
tensor power and rounding up to an integral number of bits.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Fixed-length binary tags for the summands in a power of a sum of networks. -/
noncomputable def profileSelectorTag {A t b : ℕ} (h : A ^ t ≤ 2 ^ b) :
    Fin (A ^ t) ↪ (Fin b → Bool) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using h))

/-- A single block has an integral selector width and a positive relative saving. -/
theorem exists_profile_selector_block {A D m : ℕ} (hA : 0 < A) (hD : 0 < D) (hm : 0 < m)
    {w : ℝ} (hsave : w + 2 * D * Real.logb 2 A < 2 * D * m) :
    ∃ (t b : ℕ) (ν : ℝ), 0 < t ∧ A ^ t ≤ 2 ^ b ∧ 0 < ν ∧ ν < 1 ∧
      t * w + 2 * D * b ≤ (1 - ν) * 2 * D * (t * m : ℕ) := by
  let gap := 2 * (D : ℝ) * m - (w + 2 * D * Real.logb 2 A)
  have hgap : 0 < gap := sub_pos.mpr hsave
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * D / gap)
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have htr : (0 : ℝ) < t := (div_pos (by positivity) hgap).trans ht
  have hround := (div_lt_iff₀ hgap).mp ht
  let b := ⌈(t : ℝ) * Real.logb 2 A⌉₊
  have hlog : 0 ≤ Real.logb 2 A := Real.logb_nonneg (by norm_num) (by exact_mod_cast hA)
  have hb : (b : ℝ) < t * Real.logb 2 A + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg htr.le hlog)
  have hcard : A ^ t ≤ 2 ^ b := by
    have h : Real.logb 2 ((A : ℝ) ^ t) ≤ b := by
      rw [Real.logb_pow]
      exact Nat.le_ceil _
    have h' := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
      (pow_pos (by exact_mod_cast hA) t)).mp h
    rw [Real.rpow_natCast] at h'
    exact_mod_cast h'
  let cost := t * w + 2 * D * b
  let direct := 2 * (D : ℝ) * (t * m : ℕ)
  have htpos : 0 < t := by exact_mod_cast htr
  have hdirect : 0 < direct := by
    dsimp [direct]
    positivity
  have hcost : cost < direct := by
    dsimp [cost, direct, gap] at *
    push_cast
    linarith only [hround, mul_lt_mul_of_pos_left hb (show 0 < 2 * (D : ℝ) by positivity)]
  obtain ⟨r, hrlo, hrhi⟩ := exists_between
    (max_lt ((div_lt_one hdirect).mpr hcost) zero_lt_one)
  have hratio := (div_lt_iff₀ hdirect).mp ((le_max_left _ _).trans_lt hrlo)
  refine ⟨t, b, 1 - r, htpos, hcard, sub_pos.mpr hrhi, ?_, ?_⟩
  · linarith only [(le_max_right _ _).trans_lt hrlo]
  · change cost ≤ (1 - (1 - r)) * 2 * D * (t * m : ℕ)
    simpa [direct, mul_assoc] using hratio.le

/-- Each further power retains the relative saving of the rounded block. -/
theorem profile_selector_cost_repeated {D t m b : ℕ} {w ν : ℝ}
    (h : t * w + 2 * D * b ≤ (1 - ν) * 2 * D * (t * m : ℕ)) (j : ℕ) :
    j * (t * w) + 2 * D * (j * b : ℕ) ≤ (1 - ν) * 2 * D * (j * (t * m) : ℕ) := by
  have hj := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α := ℝ) j)
  push_cast at hj ⊢
  linarith only [hj]

end SpectralBooks
end LinearAlgebra
end OAI
