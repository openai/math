import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicProgressions

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Filter Real
open Erdos970.Erdos970Dependency.SiegelWalfisz
open Erdos970.ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

/-- Dyadic primes at least seven whose predecessor has exactly one factor of two. -/
def atTwoDyadicPrimes (B : ℕ) : Finset ℕ :=
  (dyadicAxisPrimes B).filter fun p => p % 4 = 3 ∧ 7 ≤ p

private lemma atTwoDyadicPrimes_eq_interval {B : ℕ} (hB : 12 ≤ B) :
    atTwoDyadicPrimes B = intervalPrimes ((B : ℝ) / 2) (B - (B : ℝ) / 2) 4 3 := by
  ext p
  simp only [atTwoDyadicPrimes, mem_filter, mem_dyadicAxisPrimes, mem_intervalPrimes,
    add_sub_cancel]
  constructor
  · rintro ⟨⟨hp, hlo, hhi⟩, hmod, _⟩
    refine ⟨hp, (div_lt_iff₀ (by norm_num)).mpr ?_, by exact_mod_cast hhi, ?_⟩
    · exact_mod_cast (by omega : B < p * 2)
    · exact_mod_cast Int.natCast_modEq_iff.mpr (show Nat.ModEq 4 p 3 from hmod)
  · rintro ⟨hp, hlo, hhi, hmod⟩
    have hh : B < p * 2 := by exact_mod_cast (div_lt_iff₀ (by norm_num)).mp hlo
    have hm : Nat.ModEq 4 p 3 := Int.natCast_modEq_iff.mp (by exact_mod_cast hmod)
    exact ⟨⟨hp, by omega, by exact_mod_cast hhi⟩, hm, by omega⟩

/-- The dyadic interval eventually contains logarithmic mass at least `B/32`
from primes congruent to three modulo four. -/
theorem atTwoDyadicPrimes_log_mass : ∀ᶠ B : ℕ in atTop,
    (B : ℝ) / 32 ≤ ∑ p ∈ atTwoDyadicPrimes B, log p := by
  obtain ⟨K, X₀, hK, hX₀, hsw⟩ := siegel_walfisz 1 2 (by norm_num) (by norm_num)
  have ht : Tendsto (fun B : ℕ => log (B : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (max 8 (64 * K)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * X₀),
    eventually_ge_atTop 12] with B hlog hX hB
  let X := (B : ℝ)
  let L := log X
  have hL8 : 8 ≤ L := (le_max_left ..).trans hlog
  have hLlarge : 64 * K ≤ L := (le_max_right ..).trans hlog
  have hx : X₀ ≤ X / 2 := by dsimp [X]; linarith
  have hXpos : 0 < X := by linarith
  have hLpos : 0 < L := by linarith
  have hhalf : L / 2 ≤ log (X / 2) := by
    rw [log_div hXpos.ne' (by norm_num)]
    change L / 2 ≤ L - log 2
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have est (t : ℝ) (ht₀ : X₀ ≤ t) (htL : L / 2 ≤ log t) :
      |((intervalPrimes 0 t 4 3).card : ℝ) - logarithmicIntegral t / 2| ≤
        t / (32 * log t) := by
    have hlogt : 0 < log t := by linarith
    have herr := hsw t ht₀ 4 3 (by decide) ⟨-1, 1, by norm_num⟩ (by simp; linarith)
    have hφ : Nat.totient 4 = 2 := by decide
    simp only [hφ, Nat.cast_ofNat, rpow_two] at herr
    refine herr.trans ((div_le_div_iff₀ (by positivity) (by positivity)).mpr ?_)
    have hKt : 32 * K ≤ log t := by linarith
    nlinarith only [mul_le_mul_of_nonneg_right hKt (mul_nonneg (show 0 ≤ t by linarith) hlogt.le)]
  have hi := (abs_le.mp (est X (by linarith) (by dsimp [L]; linarith))).1
  have lo := (abs_le.mp (est (X / 2) hx hhalf)).2
  have hloErr : (X / 2) / (32 * log (X / 2)) ≤ X / (32 * L) := by
    apply (div_le_div_iff₀ (by nlinarith) (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hhalf hXpos.le]
  have hli := logarithmicIntegral_sub_lower (u := X / 2) (v := X) (by linarith) (by linarith)
  have hcard : X / (16 * L) ≤ (atTwoDyadicPrimes B).card := by
    rw [atTwoDyadicPrimes_eq_interval hB, intervalPrimes_count_sub (by positivity) (show X / 2 ≤ X by linarith)]
    change -(X / (32 * L)) ≤ _ at hi
    have hscale : (X - X / 2) / log X = 8 * (X / (16 * L)) := by dsimp [L]; ring
    have herr : X / (32 * L) = (X / (16 * L)) / 2 := by ring
    have hnon : 0 ≤ X / (16 * L) := by positivity
    linarith only [hi, lo, hloErr, hli, hscale, herr, hnon]
  calc
    (B : ℝ) / 32 = X / (16 * L) * (L / 2) := by change X / 32 = _; field_simp [hLpos.ne']; ring
    _ ≤ (atTwoDyadicPrimes B).card * (L / 2) := by gcongr
    _ = ∑ _p ∈ atTwoDyadicPrimes B, L / 2 := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro p hp
      have hlo := (mem_dyadicAxisPrimes.mp (mem_filter.mp hp).1).2.1
      apply hhalf.trans (log_le_log (by positivity) ?_)
      apply (div_le_iff₀ (by norm_num)).mpr
      dsimp [X]
      exact_mod_cast (by omega : B ≤ p * 2)

end FiniteFourier
end LinearAlgebra
end OAI
