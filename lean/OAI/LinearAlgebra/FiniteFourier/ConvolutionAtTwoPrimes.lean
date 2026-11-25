import OAI.LinearAlgebra.FiniteFourier.ConvolutionAtTwoProgression
import OAI.LinearAlgebra.FiniteFourier.ConvolutionOddRootOrder

/-! # Selection and packing of the prime axes at two

For the descent over the rationals with odd denominators, choose primes
congruent to three modulo four. The two orbits on each axis have odd length.
The root order is formed before choosing the axes for the packed product.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Finset Real

/-- Dyadic primes at least seven, congruent to three modulo four, whose
predecessors are smooth at the given threshold. -/
noncomputable def atTwoEligiblePrimes (B : ℕ) (η : ℝ) : Finset ℕ :=
  atTwoDyadicPrimes B ∩ smoothPredecessorPrimes B η

/-- The smooth axes in the required progression have positive lower
logarithmic mass relative to the cutoff. -/
theorem atTwoEligiblePrimes_mass :
    ∃ η c : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < c ∧
      ∀ᶠ B : ℕ in atTop, c*B ≤ ∑ p ∈ atTwoEligiblePrimes B η, log p := by
  obtain ⟨K, hK, hr⟩ := roughPredecessor_mass_bound
  let η := min (1/4) (1/(256*K))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη' : η ≤ 1/4 := min_le_left _ _
  have hKη : K*η ≤ 1/256 := by
    have h := (le_div_iff₀ (by positivity : 0 < 256*K)).mp
      (min_le_right (1/4 : ℝ) (1/(256*K)))
    dsimp [η]
    linarith only [h]
  refine ⟨η, 1/64, hη, hη', by norm_num, ?_⟩
  have ht := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [atTwoDyadicPrimes_log_mass, ht.eventually_ge_atTop (256*K),
    eventually_ge_atTop (2 : ℕ)] with B hmass hl hB
  have hBp : 1 < (B : ℝ) := by exact_mod_cast hB
  have hL := log_pos hBp
  change 256*K ≤ log (B : ℝ) at hl
  have hs : K*(η+1/log B) ≤ 1/128 := by
    have h := (div_le_iff₀ hL).mpr (show K ≤ (1/256)*log B by linarith)
    rw [mul_add, mul_one_div]
    linarith only [hKη, h]
  have hrough := hr B η hBp hη hη'
  let D := atTwoDyadicPrimes B
  let S := smoothPredecessorPrimes B η
  have hsub : D \ S ⊆ roughPredecessorPrimes B η := by
    intro p hp
    obtain ⟨hpD, hpS⟩ := mem_sdiff.mp hp
    obtain ⟨hpd, _, hp7⟩ := mem_filter.mp hpD
    obtain ⟨hpprime, _, hpB⟩ := mem_dyadicAxisPrimes.mp hpd
    have hn : ¬ ∀ l ∈ (p-1).primeFactors, (l : ℝ) ≤ (B : ℝ)^(1-η) :=
      fun h => hpS ((mem_smoothPredecessorPrimes (Nat.cast_nonneg B)).mpr
        ⟨hpprime, by omega, by exact_mod_cast hpB, h⟩)
    simp only [roughPredecessorPrimes, mem_filter, mem_erase, Nat.mem_primesLE, Nat.floor_natCast]
    exact ⟨⟨by omega, hpB, hpprime⟩, by push Not at hn; exact hn⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => log p) hsub
    (fun p hp _ => by
      obtain ⟨⟨_, _, hprim⟩, _⟩ := (by simpa only [roughPredecessorPrimes, mem_filter, mem_erase,
        Nat.mem_primesLE] using hp)
      exact log_nonneg (by exact_mod_cast Nat.Prime.one_le hprim))
  have hdecomp := sum_inter_add_sum_sdiff D S (fun p : ℕ => log p)
  change (1/64 : ℝ)*B ≤ ∑ p ∈ D ∩ S, log p
  change (B : ℝ)/32 ≤ ∑ p ∈ D, log p at hmass
  nlinarith only [hrough, hsum, hdecomp, hmass, mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg B)]

/-- The numerical and divisibility conditions in the parameter choice of
Proposition `int-positive`, with the cyclotomic degree exactly `φ(M)`. -/
theorem eventually_atTwoPrimeJetPacking :
    ∃ η c : ℝ, 0 < η ∧ η ≤ 1/4 ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      let T := log n
      let B := smoothPackingCutoff c T
      let P := atTwoEligiblePrimes B η
      let M := atTwoRootOrder P B
      Odd M ∧ (∀ k : ℕ, 3^k ≤ 8*B → 3^k ∣ M) ∧
        ∃ s : PrimeJetPacking P n M.totient B,
          (∀ p ∈ s.axes, 7 ≤ p ∧ p % 4 = 3 ∧ (p-1)/2 ∣ M) ∧
          log (8*(M.totient : ℝ)*s.jet) ≤ T^(1-η/2) := by
  obtain ⟨η, c, hη, hη', hc, hsupply⟩ := atTwoEligiblePrimes_mass
  have ht : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hb := (tendsto_smoothPackingCutoff hc).comp ht
  have hbn : Tendsto (fun n : ℕ => smoothPackingCutoff c (log n)) atTop atTop :=
    tendsto_natCast_atTop_iff.mp hb
  have hthree := (tendsto_rpow_atTop (show 0 < 1-η by linarith)).comp hb
  refine ⟨η, c, hη, hη', hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop 1,
    hb.eventually_ge_atTop 1, hthree.eventually_ge_atTop 3, hbn.eventually hsupply,
    ht.eventually (eventually_log_smoothRootOrder_jet_eight hη (by linarith) hc)] with
    n hn hT hB hcut hmass hshort
  let T := log (n : ℝ)
  let B := smoothPackingCutoff c T
  let P := atTwoEligiblePrimes B η
  let M := atTwoRootOrder P B
  change 1 ≤ T at hT
  change 1 ≤ (B : ℝ) at hB
  change (3 : ℝ) ≤ (B : ℝ)^(1-η) at hcut
  change c*B ≤ ∑ p ∈ P, log p at hmass
  change log (8*(smoothRootOrder B η : ℝ)*(8*(B : ℝ)^2+1)) ≤ T^(1-η/2) at hshort
  change Odd M ∧ _
  have hP (p : ℕ) (hp : p ∈ P) : p % 4 = 3 ∧ 7 ≤ p :=
    (mem_filter.mp (mem_inter.mp hp).1).2
  have hodd : Odd M := atTwoRootOrder_odd fun p hp => (hP p hp).1
  have he : 1 ≤ M.totient := Nat.totient_pos.mpr (by obtain ⟨k, hk⟩ := hodd; omega)
  have hMle := Nat.le_of_dvd (smoothRootOrder_pos B η) (atTwoRootOrder_dvd_smoothRootOrder
    (P := P) (fun _ hp => (mem_inter.mp hp).2) hcut)
  have heM : (M.totient : ℝ) ≤ smoothRootOrder B η := by exact_mod_cast M.totient_le.trans hMle
  have hBp : 0 < (B : ℝ) := by linarith
  have hMp : 0 < (smoothRootOrder B η : ℝ) := by exact_mod_cast smoothRootOrder_pos B η
  have hep : 0 < (M.totient : ℝ) := by exact_mod_cast he
  have hbudget : (M.totient : ℝ)*(B : ℝ)^2 ≤ n := by
    apply (log_le_log_iff (by positivity) (by exact_mod_cast hn)).mp
    calc
      _ ≤ log (8*(smoothRootOrder B η : ℝ)*(8*(B : ℝ)^2+1)) := by
        apply log_le_log (by positivity)
        calc
          _ ≤ (smoothRootOrder B η : ℝ)*(B : ℝ)^2 := by gcongr
          _ ≤ _ := by nlinarith only [mul_nonneg hMp.le (sq_nonneg (B : ℝ)), hMp.le]
      _ ≤ T^(1-η/2) := hshort
      _ ≤ T := (rpow_le_rpow_of_exponent_le hT (by linarith : 1-η/2 ≤ 1)).trans_eq (rpow_one T)
  have hpf (p : ℕ) (hp : p ∈ P) : p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ B := by
    obtain ⟨h₁, h₂, h₃, _⟩ := (mem_smoothPredecessorPrimes (Nat.cast_nonneg B)).mp (mem_inter.mp hp).2
    exact ⟨h₁,h₂,h₃⟩
  have hmass' : 2*log n < ∑ p ∈ P, log p := by
    have h := (div_le_iff₀ hc).mp (Nat.le_ceil (3*T/c))
    change 3*T ≤ B*c at h
    change 2*T < _
    linarith
  obtain ⟨s⟩ := exists_primeJetPacking P hn he hpf hmass' hbudget
  refine ⟨hodd, fun _ hk => three_pow_dvd_atTwoRootOrder hk, s, ?_, ?_⟩
  · intro p hp
    have hm := s.axes_subset hp
    exact ⟨(hP p hm).2, (hP p hm).1, half_predecessor_dvd_atTwoRootOrder hm⟩
  · refine le_trans ?_ hshort
    apply log_le_log
    · have hj := hBp.trans_le s.jet_lower
      positivity
    · gcongr
      exact s.jet_upper

end FiniteFourier
end LinearAlgebra
end OAI
