import OAI.LinearAlgebra.FiniteFourier.WorkingPrimes
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

/-! # Coprime working lengths for the geometric-grid algorithm

A prefix of the available small primes is padded by a single radix power.
The chosen working length is within a factor of three of the requested
convolution length and all its factors are small and prime to the characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Finset Polynomial

/-- The radix is three in characteristic two and two in every other characteristic. -/
noncomputable def fourierRadix (K : Type*) [Field K] : ℕ := if ringChar K = 2 then 3 else 2

theorem fourierRadix_prime (K : Type*) [Field K] : Nat.Prime (fourierRadix K) := by
  unfold fourierRadix
  split <;> decide

theorem fourierRadix_le_three (K : Type*) [Field K] : fourierRadix K ≤ 3 := by
  unfold fourierRadix
  split <;> decide

theorem fourierRadix_cast_ne_zero (K : Type*) [Field K] : (fourierRadix K : K) ≠ 0 := by
  unfold fourierRadix
  split <;> rename_i h
  · intro hz
    have := CharP.ringChar_of_prime_eq_zero Nat.prime_three hz
    omega
  · intro hz
    exact h (CharP.ringChar_of_prime_eq_zero Nat.prime_two hz)

private theorem exists_crossing_factor {k : ℕ} (hk : 1 < k) (s : Finset ℕ)
    (hs : k ≤ ∏ p ∈ s, p) :
    ∃ u ⊆ s, ∃ p ∈ s, p ∉ u ∧ (∏ q ∈ u, q) < k ∧ k ≤ (∏ q ∈ u, q) * p := by
  induction s using Finset.induction_on with
  | empty => simp at hs; omega
  | @insert x s hx ih =>
    by_cases hc : k ≤ ∏ p ∈ s, p
    · obtain ⟨u, hu, p, hp, hpu, hlt, hle⟩ := ih hc
      exact ⟨u, hu.trans (subset_insert _ _), p, mem_insert_of_mem hp, hpu, hlt, hle⟩
    · rw [prod_insert hx, mul_comm] at hs
      exact ⟨s, subset_insert _ _, x, mem_insert_self .., hx, lt_of_not_ge hc, hs⟩

/-- Least radix padding brings `P` up to the target `k`. Its exponent is positive and the
working length is still strictly below `k * ℓ`. -/
theorem exists_radix_padding {ℓ k P : ℕ} (hℓ : 1 < ℓ) (hP : 0 < P) (hPk : P < k) :
    ∃ j : ℕ, 0 < j ∧ k ≤ P * ℓ ^ j ∧ P * ℓ ^ j < k * ℓ ∧
      ∀ i < j, P * ℓ ^ i < k := by
  have hex : ∃ j : ℕ, k ≤ P * ℓ ^ j :=
    ⟨k, (Nat.lt_pow_self hℓ).le.trans (Nat.le_mul_of_pos_left _ hP)⟩
  have hge := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    by_contra! hn
    have hzero := Nat.eq_zero_of_le_zero hn
    simp [hzero] at hge
    omega
  have hmin : ∀ i < Nat.find hex, P * ℓ ^ i < k := fun i hi ↦ lt_of_not_ge (Nat.find_min hex hi)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  refine ⟨Nat.find hex, hpos, hge, ?_, hmin⟩
  rw [hm, pow_succ, ← mul_assoc]
  exact Nat.mul_lt_mul_of_pos_right (hmin m (by omega)) (by omega)

/-- A factorization of the working length into small coprime orders. -/
structure WorkingFactors (K : Type*) [Field K] (a t : ℕ) where
  factors : Finset ℕ
  factor_ge : ∀ d ∈ factors, 2 ≤ d
  factor_le : ∀ d ∈ factors, d ≤ 3 * t ^ 2
  cast_ne_zero : ∀ d ∈ factors, (d : K) ≠ 0
  pairwise : (factors : Set ℕ).Pairwise Nat.Coprime
  lower : 2 * a ≤ ∏ d ∈ factors, d
  upper : (∏ d ∈ factors, d) < 6 * a

/-- Construct the manuscript's working length from any sufficiently long list of
available primes. The omitted characteristic also allows characteristic zero. -/
theorem exists_workingFactors_of_primes (K : Type*) [Field K] {a t : ℕ} (ha : 2 ≤ a)
    (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime ∧ p ≤ t ^ 2 ∧
      p ≠ fourierRadix K ∧ p ≠ ringChar K) (hbig : 2 * a ≤ ∏ p ∈ s, p) :
    Nonempty (WorkingFactors K a t) := by
  let ℓ := fourierRadix K
  have hpℓ : ℓ.Prime := fourierRadix_prime K
  have hℓ : ℓ ≤ 3 := fourierRadix_le_three K
  obtain ⟨u, hus, p, hps, -, hlt, hle⟩ := exists_crossing_factor (by omega) s hbig
  let P := ∏ q ∈ u, q
  have hP : 0 < P := Finset.prod_pos fun q hq ↦ (hprime q (hus hq)).1.pos
  obtain ⟨j, hj, hlo, hup, hmin⟩ := exists_radix_padding hpℓ.one_lt hP hlt
  have hsmall : ℓ ^ j ≤ 3 * t ^ 2 := by
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hprev : ℓ ^ i < p := Nat.lt_of_mul_lt_mul_left ((hmin i (by omega)).trans_le hle)
    rw [hi, pow_succ, mul_comm]
    exact Nat.mul_le_mul hℓ (hprev.le.trans (hprime p hps).2.1)
  have hco (q : ℕ) (hq : q ∈ u) : q.Coprime (ℓ ^ j) := by
    obtain ⟨hqp, -, hne, -⟩ := hprime q (hus hq)
    exact ((Nat.coprime_primes hqp hpℓ).mpr hne).pow_right _
  have hq1 : 1 < ℓ ^ j := one_lt_pow₀ hpℓ.one_lt hj.ne'
  have hnew : ℓ ^ j ∉ u := fun hy ↦ hq1.ne' (by simpa [Nat.Coprime] using (hco _ hy))
  refine ⟨⟨insert (ℓ ^ j) u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d hd
    rcases mem_insert.mp hd with rfl | hu
    · omega
    · exact (hprime _ (hus hu)).1.two_le
  · intro d hd
    rcases mem_insert.mp hd with rfl | hu
    · exact hsmall
    · have := (hprime _ (hus hu)).2.1; omega
  · intro d hd
    rcases mem_insert.mp hd with rfl | hu
    · simpa using pow_ne_zero j (fourierRadix_cast_ne_zero K)
    · obtain ⟨hqp, -, -, hchar⟩ := hprime _ (hus hu)
      exact fun hz ↦ hchar (CharP.ringChar_of_prime_eq_zero hqp hz).symm
  · intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
    · exact (hxy rfl).elim
    · exact (hco _ hy).symm
    · exact hco _ hx
    · exact (Nat.coprime_primes (hprime _ (hus hx)).1 (hprime _ (hus hy)).1).mpr hxy
  · simpa [prod_insert hnew, P, mul_comm] using hlo
  · rw [prod_insert hnew, mul_comm]
    exact hup.trans_le (by nlinarith)

/-- The least radix power sufficient for the short transform on a factor of size `d`. -/
theorem exists_short_radix_order (K : Type*) [Field K] {d : ℕ} (hd : 2 ≤ d) :
    ∃ j : ℕ, 2 * d ≤ fourierRadix K ^ j ∧ fourierRadix K ^ j < 6 * d ∧
      (∀ i < j, fourierRadix K ^ i < 2 * d) := by
  obtain ⟨j, -, h, hu, hm⟩ := exists_radix_padding (fourierRadix_prime K).one_lt
    (P := 1) (by decide) (show 1 < 2 * d by omega)
  simp only [one_mul] at h hu hm
  exact ⟨j, h, hu.trans_le (by nlinarith [fourierRadix_le_three K]), hm⟩

/-- All axis sizes at most `N` have admissible working lengths, uniformly in the field,
when the group size `N` is sufficiently large. -/
theorem eventually_exists_workingFactors :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (K : Type*) [Field K] (a : ℕ), 2 ≤ a → a ≤ N →
      Nonempty (WorkingFactors K a (Nat.clog 2 N)) := by
  have hlim : Filter.Tendsto (Nat.clog 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.mpr (fun k ↦ ?_)
    filter_upwards [Filter.eventually_ge_atTop (2 ^ k)] with N hN
    simpa [Nat.clog_pow _ _ (by decide : 1 < 2)] using Nat.clog_mono_right 2 hN
  filter_upwards [hlim.eventually eventually_two_mul_lt_prod_workingPrimes] with N hN K _ a ha hau
  let s := workingPrimes (Nat.clog 2 N) (fourierRadix K) (ringChar K)
  refine exists_workingFactors_of_primes K ha s ?_ ?_
  · intro p hp
    exact ⟨(mem_workingPrimes.mp hp).1, (mem_workingPrimes.mp hp).2.2⟩
  · exact (Nat.mul_le_mul_left 2 hau).trans (hN _ _ N (Nat.le_pow_clog (by decide : 1 < 2) N)).le

/-- The field generated by a primitive `M`th root has degree at most `M` over
the base field, even when the cyclotomic polynomial is reducible there. -/
theorem working_cyclotomic_finrank_le (K : Type*) [Field K] {M : ℕ} [NeZero M] [NeZero (M : K)] :
    Module.finrank K (CyclotomicField M K) ≤ M := by
  let ζ := IsCyclotomicExtension.zeta M K (CyclotomicField M K)
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M K _
  rw [(hζ.powerBasis K).finrank, hζ.powerBasis_dim K]
  have hd : minpoly K ζ ∣ (X ^ M - C (1 : K)) := minpoly.dvd K ζ (by simp [hζ.pow_eq_one])
  simpa only [natDegree_X_pow_sub_C] using Polynomial.natDegree_le_of_dvd hd (X_pow_sub_C_ne_zero (NeZero.pos _) (1 : K))

/-- Auxiliary Fourier roots of every divisor order are powers of the same generator. -/
theorem working_cyclotomic_root (K : Type*) [Field K] {M k : ℕ} [NeZero M] [NeZero (M : K)]
    (hk : k ∣ M) :
    IsPrimitiveRoot (IsCyclotomicExtension.zeta M K (CyclotomicField M K) ^ (M / k)) k :=
  (IsCyclotomicExtension.zeta_spec M K _).pow (NeZero.pos _) (Nat.div_mul_cancel hk).symm

end FiniteFourier
end LinearAlgebra
end OAI
