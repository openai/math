import OAI.LinearAlgebra.FiniteFourier.ConvolutionTotientHarmonic
import OAI.NumberTheory.TotientAsymptotic.UniformPrimePairBound
import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeSupply
import Mathlib.Tactic

/-! # Primes with smooth predecessors

The smoothness cutoff is real. We express the largest-prime-factor test by
quantifying over the finite set of prime divisors of the predecessor. The
Selberg estimate for the two linear polynomials is uniform in the cofactor.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology

section

/-- Odd primes up to the real cutoff with a prime factor of the predecessor
strictly above the smoothness threshold. -/
def roughPredecessorPrimes (B η : ℝ) : Finset ℕ :=
  ((Nat.primesLE ⌊B⌋₊).erase 2).filter fun p ↦
    ∃ q ∈ (p - 1).primeFactors, B ^ (1 - η) < (q : ℝ)

/-- Odd primes up to the real cutoff whose predecessor is smooth at the
threshold of Lemma `poly:lem:elementary-supply`. -/
def smoothPredecessorPrimes (B η : ℝ) : Finset ℕ :=
  ((Nat.primesLE ⌊B⌋₊).erase 2).filter fun p ↦
    ∀ q ∈ (p - 1).primeFactors, (q : ℝ) ≤ B ^ (1 - η)

lemma mem_smoothPredecessorPrimes {B η : ℝ} (hB : 0 ≤ B) {p : ℕ} :
    p ∈ smoothPredecessorPrimes B η ↔
      p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ B ∧
        ∀ q ∈ (p - 1).primeFactors, (q : ℝ) ≤ B ^ (1 - η) := by
  simp only [smoothPredecessorPrimes, mem_filter, mem_erase, Nat.mem_primesLE, Nat.le_floor_iff hB]
  constructor
  · rintro ⟨⟨hne, hpB, hp⟩, hs⟩
    exact ⟨hp, by have := hp.two_le; omega, hpB, hs⟩
  · rintro ⟨hp, hp₃, hpB, hs⟩
    exact ⟨⟨by omega, hpB, hp⟩, hs⟩

private lemma rough_card_le_pairs {B η : ℝ} (hB : 1 < B) :
    (roughPredecessorPrimes B η).card ≤
      ∑ h ∈ Icc 1 ⌊B ^ η⌋₊, (TotientAsymptotic.allShiftedPrimePairs h ⌈B / h⌉₊).card := by
  let pairs (h : ℕ) := TotientAsymptotic.allShiftedPrimePairs h ⌈B / h⌉₊
  let images (h : ℕ) := (pairs h).image (fun q ↦ h*q+1)
  have hsub : roughPredecessorPrimes B η ⊆ (Icc 1 ⌊B ^ η⌋₊).biUnion images := by
    intro p hp
    simp only [roughPredecessorPrimes, mem_filter] at hp
    obtain ⟨hp', q, hq, hbig⟩ := hp
    obtain ⟨hp₂, hp'⟩ := mem_erase.mp hp'
    obtain ⟨hpB, hprime⟩ := Nat.mem_primesLE.mp hp'
    obtain ⟨hqprime, ⟨h, heq⟩, _⟩ := Nat.mem_primeFactors.mp hq
    have he : h*q+1 = p := by rw [mul_comm, ← heq]; have := hprime.pos; omega
    have hh : 0 < h := by
      by_contra! hh
      have hz : h = 0 := by omega
      have := hprime.two_le
      simp [hz] at he
      omega
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    have hpR : (p : ℝ) ≤ B := (Nat.le_floor_iff (by linarith)).mp hpB
    have hm : (h : ℝ)*q ≤ B := by
      have : (↑(h*q+1) : ℝ) ≤ B := he ▸ hpR
      push_cast at this
      linarith
    have hfac : B ^ η * B ^ (1-η) = B := by
      rw [← Real.rpow_add (by linarith : 0 < B)]
      simp
    have hcut : (h : ℝ) ≤ B ^ η := by
      apply le_of_mul_le_mul_right (a := B ^ (1-η)) _ (Real.rpow_pos_of_pos (by linarith) _)
      rw [hfac]
      exact (mul_le_mul_of_nonneg_left hbig.le hhR.le).trans hm
    have hqcut : q ≤ ⌈B / h⌉₊ := by
      apply (Nat.cast_le (α := ℝ)).mp
      exact ((le_div_iff₀ hhR).mpr (by simpa [mul_comm] using hm)).trans (Nat.le_ceil _)
    apply mem_biUnion.mpr
    refine ⟨h, mem_Icc.mpr ⟨hh, Nat.le_floor hcut⟩, mem_image.mpr ⟨q, ?_, he⟩⟩
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hqprime.one_le, hqcut⟩, hqprime, he.symm ▸ hprime⟩
  exact (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_image_le))

private lemma pair_log_mass_le {B η C : ℝ} (hB : 1 < B) (hη : η ≤ 1/4) (hC : 0 < C)
    (hsieve : ∀ h : ℕ, 0 < h → ∀ X : ℕ, 2 ≤ X →
      ((TotientAsymptotic.allShiftedPrimePairs h X).card : ℝ) ≤
        C * X * ((h : ℝ)/h.totient) / (log X)^2)
    {h : ℕ} (hh : h ∈ Icc 1 ⌊B ^ η⌋₊) :
    ((TotientAsymptotic.allShiftedPrimePairs h ⌈B / h⌉₊).card : ℝ) * log B ≤
      8*C*B/log B * (h.totient : ℝ)⁻¹ := by
  obtain ⟨hh₁, hh₂⟩ := mem_Icc.mp hh
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh₁
  have hbpos : 0 < B := by linarith
  have hlog := log_pos hB
  have hexp : 0 < 1-η := by linarith
  have hcut : (h : ℝ) ≤ B ^ η := (Nat.le_floor_iff (Real.rpow_nonneg hbpos.le _)).mp hh₂
  have hpow : B ^ (1-η) ≤ B / h := by
    apply (le_div_iff₀ hhpos).mpr
    calc
      _ ≤ B ^ (1-η)*B ^ η := mul_le_mul_of_nonneg_left hcut (Real.rpow_nonneg hbpos.le _)
      _ = B := by rw [← Real.rpow_add hbpos]; simp
  let X := ⌈B / h⌉₊
  have hx : 1 < B / h := (Real.one_lt_rpow hB hexp).trans_le hpow
  have hx₁ : 1 < X := Nat.lt_ceil.mpr (by simpa using hx)
  have hxlog : log B / 2 ≤ log X := by
    have hhlog := log_le_log (Real.rpow_pos_of_pos hbpos _) (hpow.trans (Nat.le_ceil _))
    rw [log_rpow hbpos] at hhlog
    nlinarith [mul_nonneg (show 0 ≤ 1/2-η by linarith) hlog.le]
  have hxupper : (X : ℝ) ≤ 2*B/h := by
    have hl := Nat.ceil_lt_add_one (by linarith : 0 ≤ B / h)
    change (↑⌈B / h⌉₊ : ℝ) ≤ _
    rw [mul_div_assoc]
    linarith
  have hφ : (0 : ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr hh₁
  calc
    _ ≤ (C * X * ((h : ℝ)/h.totient) / (log X)^2) * log B :=
      mul_le_mul_of_nonneg_right (hsieve h hh₁ X hx₁) hlog.le
    _ ≤ (C * (2*B/h) * ((h : ℝ)/h.totient) / (log B/2)^2) * log B := by
      apply mul_le_mul_of_nonneg_right _ hlog.le
      apply div_le_div₀ (by positivity) _ (by positivity)
        (pow_le_pow_left₀ (by positivity) hxlog 2)
      gcongr
    _ = _ := by field_simp; ring

/-- The Selberg bound after summing over all possible cofactors. It controls the
number of discarded primes even when some of them are small. -/
theorem roughPredecessor_card_mul_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B η : ℝ, 1 < B → 0 < η → η ≤ 1/4 →
      ((roughPredecessorPrimes B η).card : ℝ) * log B ≤ K*B*(η + 1/log B) := by
  obtain ⟨C, hC, hsieve⟩ := TotientAsymptotic.uniform_prime_pair_bound
  obtain ⟨D, hD, htot⟩ := exists_reciprocal_totient_sum_bound
  refine ⟨8*C*D, by positivity, ?_⟩
  intro B η hB hη hη'
  let H := ⌊B ^ η⌋₊
  have hbpos : 0 < B := by linarith
  have hlog := log_pos hB
  have hpow := Real.one_le_rpow hB.le hη.le
  have hH : 1 ≤ H := Nat.le_floor (by simpa using hpow)
  have hHlog : log H ≤ η*log B := by
    rw [← log_rpow hbpos]
    exact log_le_log (by exact_mod_cast hH) (Nat.floor_le (by positivity))
  have hcard : ((roughPredecessorPrimes B η).card : ℝ) ≤
      ∑ h ∈ Icc 1 H, ((TotientAsymptotic.allShiftedPrimePairs h ⌈B / h⌉₊).card : ℝ) := by
    exact_mod_cast rough_card_le_pairs (η := η) hB
  calc
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hlog.le
    _ = _ := sum_mul ..
    _ ≤ ∑ h ∈ Icc 1 H, 8*C*B/log B * (h.totient : ℝ)⁻¹ :=
      sum_le_sum fun _ hh ↦ pair_log_mass_le hB hη' hC hsieve hh
    _ = _ := (mul_sum ..).symm
    _ ≤ 8*C*B/log B * (D*(1+log H)) := mul_le_mul_of_nonneg_left (htot H hH) (by positivity)
    _ ≤ 8*C*B/log B * (D*(1+η*log B)) := by gcongr
    _ = _ := by field_simp; ring

/-- The uniform estimate for the discarded logarithmic mass in
Lemma `poly:lem:elementary-supply`. -/
theorem roughPredecessor_mass_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ B η : ℝ, 1 < B → 0 < η → η ≤ 1/4 →
      (∑ p ∈ roughPredecessorPrimes B η, log p) ≤ K*B*(η + 1/log B) := by
  obtain ⟨K, hK, hcard⟩ := roughPredecessor_card_mul_log_bound
  refine ⟨K, hK, ?_⟩
  intro B η hB hη hη'
  have hbpos : 0 < B := by linarith
  calc
    _ ≤ (roughPredecessorPrimes B η).card * log B := by
      simpa using sum_le_card_nsmul (roughPredecessorPrimes B η) (fun p ↦ log p) (log B)
        (fun p hp ↦ by
          simp only [roughPredecessorPrimes, mem_filter, mem_erase, Nat.mem_primesLE] at hp
          obtain ⟨hpB, hprime⟩ := hp.1.2
          exact log_le_log (by exact_mod_cast hprime.pos) ((Nat.le_floor_iff hbpos.le).mp hpB))
    _ ≤ _ := hcard B η hB hη hη'

private lemma predecessor_mass_partition {B η : ℝ} (hB : 2 ≤ B) :
    (∑ p ∈ smoothPredecessorPrimes B η, log p) +
      (∑ p ∈ roughPredecessorPrimes B η, log p) + log 2 = Chebyshev.theta B := by
  have htwo : 2 ∈ Nat.primesLE ⌊B⌋₊ :=
    Nat.mem_primesLE.mpr ⟨Nat.le_floor (by simpa using hB), Nat.prime_two⟩
  have hpartition := sum_filter_add_sum_filter_not ((Nat.primesLE ⌊B⌋₊).erase 2)
    (fun p ↦ ∀ q ∈ (p-1).primeFactors, (q : ℝ) ≤ B ^ (1-η)) (fun p ↦ log p)
  rw [Chebyshev.theta_eq_sum_primesLE, ← sum_erase_add _ _ htwo]
  simpa [smoothPredecessorPrimes, roughPredecessorPrimes, and_assoc] using
    congrArg (fun x : ℝ ↦ x + log 2) hpartition

/-- Lemma `poly:lem:elementary-supply`. Chebyshev's elementary lower bound
leaves positive logarithmic mass after fixing the smoothness exponent. -/
theorem smoothPredecessor_prime_supply :
    ∃ η c₀ : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < c₀ ∧
      ∀ᶠ B : ℝ in atTop, c₀*B ≤ ∑ p ∈ smoothPredecessorPrimes B η, log p := by
  obtain ⟨K, hK, hbound⟩ := roughPredecessor_mass_bound
  let η := min (1/4) (1/(32*K))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη' : η ≤ 1/4 := min_le_left _ _
  have hηK : K*η ≤ 1/32 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32*K)).mp (min_le_right (1/4:ℝ) (1/(32*K)))
    dsimp [η]
    linarith
  refine ⟨η, 1/8, hη, hη', by norm_num, ?_⟩
  filter_upwards [TwoPointCorrelations.halasz_theta_eventually_lower,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32*K)),
    eventually_ge_atTop (2:ℝ), eventually_ge_atTop (16*log (2:ℝ))] with B hθ hl hB hB'
  have hBp : 0 < B := by linarith
  have hlog := log_pos (by linarith : 1 < B)
  have hinv : K / log B ≤ 1/32 := (div_le_iff₀ hlog).mpr (by linarith)
  have hsmall : K * (η + 1/log B) ≤ 1/16 := by
    rw [mul_add, mul_one_div]
    linarith
  have h := hbound B η (by linarith) hη hη'
  have hmul := mul_le_mul_of_nonneg_right hsmall hBp.le
  have hp := predecessor_mass_partition (η := η) hB
  nlinarith only [h, hθ, hp, hB', hmul]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
