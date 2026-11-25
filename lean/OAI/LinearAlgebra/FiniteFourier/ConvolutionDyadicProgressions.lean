import OAI.NumberTheory.Jacobsthal.Estimates.SiegelWalfisz
import OAI.NumberTheory.Jacobsthal.Primes.PrimeIntervalFlags

/-! # Dyadic prime counts in small arithmetic progressions

Apply the project's Siegel–Walfisz theorem at both ends of the dyadic
interval. The same estimate with modulus one compares each progression
directly with the total number of primes in that interval.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Filter Real
open Erdos970.Erdos970Dependency.SiegelWalfisz
open Erdos970.ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral)

/-- Primes in the half-open interval `(B/2,B]`. -/
def dyadicAxisPrimes (B : ℕ) : Finset ℕ := (Ioc (B / 2) B).filter Nat.Prime

@[simp] theorem mem_dyadicAxisPrimes {B p : ℕ} :
    p ∈ dyadicAxisPrimes B ↔ p.Prime ∧ B < 2 * p ∧ p ≤ B := by
  simp only [dyadicAxisPrimes, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨hl, hu⟩, hp⟩
    exact ⟨hp, by omega, hu⟩
  · rintro ⟨hp, hl, hu⟩
    exact ⟨⟨by omega, hu⟩, hp⟩

/-- Dyadic primes whose predecessor is divisible by the given modulus. -/
def axisShiftFibre (B q : ℕ) : Finset ℕ := (dyadicAxisPrimes B).filter fun p => q ∣ p - 1

private theorem axisShiftFibre_one (B : ℕ) : axisShiftFibre B 1 = dyadicAxisPrimes B := by
  simp [axisShiftFibre]

private theorem axisShiftFibre_eq_interval (B q : ℕ) :
    axisShiftFibre B q = intervalPrimes ((B : ℝ)/2) (B - (B : ℝ)/2) q 1 := by
  ext p
  simp only [axisShiftFibre, mem_filter, mem_dyadicAxisPrimes, mem_intervalPrimes, add_sub_cancel]
  constructor
  · rintro ⟨⟨hp, hlo, hhi⟩, hmod⟩
    refine ⟨hp, ?_, by exact_mod_cast hhi, ?_⟩
    · exact (div_lt_iff₀ (by norm_num)).mpr (by exact_mod_cast (by omega : B < p * 2))
    · have h := ((Nat.modEq_iff_dvd' hp.one_le).mpr hmod).symm
      exact_mod_cast Int.natCast_modEq_iff.mpr h
  · rintro ⟨hp, hlo, hhi, hmod⟩
    refine ⟨⟨hp, ?_, by exact_mod_cast hhi⟩, ?_⟩
    · have hh := (div_lt_iff₀ (by norm_num)).mp hlo
      have : B < p * 2 := by exact_mod_cast hh
      omega
    · apply (Nat.modEq_iff_dvd' hp.one_le).mp
      apply Nat.ModEq.symm
      apply Int.natCast_modEq_iff.mp
      exact_mod_cast hmod

/-- A common error bound covers both the ordinary dyadic count and all
progressions of prime modulus at most the fourth power of the logarithm. -/
theorem eventually_dyadicPrimeProgression_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      (B : ℝ) / (4 * log B) ≤ (dyadicAxisPrimes B).card ∧
      ∀ l : ℕ, l.Prime → 3 ≤ l → (l : ℝ) ≤ (log B) ^ 4 →
        ((axisShiftFibre B l).card : ℝ) ≤
          (dyadicAxisPrimes B).card / ((l : ℝ) - 1) + C * B / (log B) ^ 6 := by
  obtain ⟨K, X₀, hK, hX₀, hsw⟩ := siegel_walfisz 6 6 (by norm_num) (by norm_num)
  refine ⟨66 * K, by positivity, ?_⟩
  have hL : Tendsto (fun B : ℕ => log (B : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL.eventually_ge_atTop (max 8 (132 * K)),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * X₀)] with B hLB hXB
  let X := (B : ℝ)
  let L := log X
  have hL8 : 8 ≤ L := (le_max_left ..).trans hLB
  have hlarge : 132 * K ≤ L := (le_max_right ..).trans hLB
  have hLpos : 0 < L := by linarith
  have hx : X₀ ≤ X / 2 := by dsimp [X]; linarith
  have hXpos : 0 < X := by linarith
  have hlogHalf : L / 2 ≤ log (X / 2) := by
    rw [log_div hXpos.ne' (by norm_num)]
    change L / 2 ≤ L - log 2
    linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hhalf : 0 < L / 2 := by positivity
  have hpow : L ^ 4 ≤ (L / 2) ^ 6 := by
    have hs : 64 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 8)]
    nlinarith only [mul_le_mul_of_nonneg_left hs (pow_nonneg hLpos.le 4)]
  let D := logarithmicIntegral X - logarithmicIntegral (X / 2)
  let E := 33 * K * X / L ^ 6
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have herr (q : ℕ) (hq : 0 < q) (hb : (q : ℝ) ≤ L ^ 4) :
      |((axisShiftFibre B q).card : ℝ) - D / q.totient| ≤ E := by
    have estimate (t : ℝ) (ht : X₀ ≤ t) (hlt : (q : ℝ) ≤ (log t) ^ (6 : ℕ)) :
        |((intervalPrimes 0 t q 1).card : ℝ) - logarithmicIntegral t / q.totient| ≤
          K * t / (log t) ^ (6 : ℕ) := by
      have h := hsw t ht q 1 hq isCoprime_one_left (by simpa using hlt)
      simpa using h
    have hhalfBound := hb.trans (hpow.trans (pow_le_pow_left₀ hhalf.le hlogHalf 6))
    have hfullBound := hb.trans (hpow.trans (pow_le_pow_left₀ hhalf.le (show L / 2 ≤ L by linarith) 6))
    have eX := estimate X (by linarith) hfullBound
    have eY := estimate (X / 2) hx hhalfBound
    have hhalfError : K * (X / 2) / (log (X / 2)) ^ (6 : ℕ) ≤ 32 * K * X / L ^ 6 := calc
      _ ≤ K * (X / 2) / (L / 2) ^ (6 : ℕ) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hhalf.le hlogHalf _)
      _ = _ := by rw [div_pow]; ring
    rw [axisShiftFibre_eq_interval, intervalPrimes_count_sub (by positivity) (show X / 2 ≤ X by linarith)]
    change |(_ - _) - (logarithmicIntegral X - logarithmicIntegral (X / 2)) / _| ≤ E
    rw [sub_div]
    calc
      _ = |(((intervalPrimes 0 X q 1).card : ℝ) - logarithmicIntegral X / q.totient) -
          (((intervalPrimes 0 (X / 2) q 1).card : ℝ) - logarithmicIntegral (X / 2) / q.totient)| := by
            congr 1
            ring
      _ ≤ _ := (abs_sub ..).trans <| (add_le_add eX (eY.trans hhalfError)).trans (by dsimp [E, L]; ring_nf; rfl)
  have hone := herr 1 (by decide) (by simpa using (one_le_pow₀ (n := 4) (show 1 ≤ L by linarith)))
  simp only [axisShiftFibre_one, Nat.totient_one, Nat.cast_one, div_one, abs_le] at hone
  constructor
  · have hli : (X - X / 2) / L ≤ D := logarithmicIntegral_sub_lower (by linarith) (by linarith)
    have hscale : 132 * K ≤ L ^ 5 := hlarge.trans (by
      have := one_le_pow₀ (n := 4) (show 1 ≤ L by linarith)
      nlinarith only [mul_le_mul_of_nonneg_left this hLpos.le])
    have he : E ≤ X / (4 * L) := by
      dsimp [E]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hXpos.le hLpos.le)
      nlinarith only [hh]
    change X / (4 * L) ≤ _
    have hh : (X - X / 2) / L = 2 * (X / (4 * L)) := by ring
    linarith only [hh, hli, hone.1, he]
  · intro l hl hl₃ hlB
    have he := (abs_le.mp (herr l hl.pos hlB)).2
    rw [Nat.totient_prime hl, Nat.cast_sub hl.one_le, Nat.cast_one] at he
    have hden : (1 : ℝ) ≤ (l : ℝ) - 1 := by
      have : (3 : ℝ) ≤ l := by exact_mod_cast hl₃
      linarith
    have hd := div_le_div_of_nonneg_right (show D ≤ (dyadicAxisPrimes B).card + E by linarith only [hone.1])
      (by linarith : 0 ≤ (l : ℝ) - 1)
    rw [add_div] at hd
    have hEdiv := div_le_self hE hden
    have hh : 66 * K * B / (log B) ^ 6 = 2 * E := by dsimp [E, L, X]; ring
    linarith only [hh, hd, he, hEdiv]

end FiniteFourier
end LinearAlgebra
end OAI
