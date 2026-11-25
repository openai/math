import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimeCollisions
import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicErrors

/-! # Large dyadic lists of primes with disjoint odd supports

The uniform sieve for rough predecessors and the estimates for small
progressions leave a positive proportion of the ordered pairs of dyadic
primes. Coloring their odd supports then produces both lists simultaneously.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Finset Real

private lemma eventually_power_le_div_log {s : ℝ} (hs : 0 < s) :
    ∀ᶠ B : ℕ in atTop, 16 * (B : ℝ) ^ (1-s) ≤ B / (4 * log B) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop hs).bound (show (0 : ℝ) < 1/64 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℕ)] with B h hB
  have hpos : (1 : ℝ) < B := by exact_mod_cast hB
  have hlog := log_pos hpos
  have hbound : log B ≤ (1/64) * (B : ℝ)^s := by
    simpa only [Real.norm_of_nonneg hlog.le, Real.norm_of_nonneg (Real.rpow_nonneg
      (Nat.cast_nonneg B) _)] using h
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = 64 * (B : ℝ) ^ (1-s) * log B := by ring
    _ ≤ 64 * (B : ℝ) ^ (1-s) * ((1/64) * (B : ℝ)^s) := by gcongr
    _ = (B : ℝ) ^ (1-s) * (B : ℝ)^s := by ring
    _ = (B : ℝ) := by rw [← Real.rpow_add (by positivity), sub_add_cancel, Real.rpow_one]

/-- There are `B^(2-o(1))` eligible dyadic pairs with disjoint odd supports
for a single fixed positive smoothness exponent. -/
theorem dyadicDisjointPairs_supply :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ B : ℕ in atTop,
      (B : ℝ) ^ (2-δ) ≤ (dyadicDisjointPairs B η).card := by
  obtain ⟨K, hK, hr⟩ := roughPredecessor_card_mul_log_bound
  obtain ⟨C, hC, hp⟩ := eventually_dyadicPrimeProgression_bounds
  let η := min (1/4) (1/(512*K))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη' : η ≤ 1/4 := min_le_left _ _
  have hKη : K * η ≤ 1/512 := by
    have h := (le_div_iff₀ (by positivity : 0 < 512*K)).mp
      (min_le_right (1/4 : ℝ) (1/(512*K)))
    dsimp [η]
    linarith only [h]
  refine ⟨η, hη, hη', ?_⟩
  intro δ hδ
  have htop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, eventually_ge_atTop (8 : ℕ), htop.eventually_ge_atTop (512*K),
    htop.eventually_ge_atTop (64*(C+1)), eventually_power_le_div_log (s := 1) zero_lt_one,
    eventually_power_le_div_log (half_pos hδ)] with B hpr hB hLK hLC hlarge hpower
  let L := log (B : ℝ)
  let D : ℝ := (dyadicAxisPrimes B).card
  let R : ℝ := (roughPredecessorPrimes B η).card
  let G : ℝ := (dyadicDisjointPairs B η).card
  let H := ⌊L^4⌋₊
  let a := C * B / L^6
  change 512*K ≤ L at hLK
  change 64*(C+1) ≤ L at hLC
  obtain ⟨hcount, hfibre⟩ := hpr
  change (B : ℝ)/(4*L) ≤ D at hcount
  have hL : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hBp : 1 < (B : ℝ) := by exact_mod_cast (by omega : 1 < B)
  have hD : 16 ≤ D := by
    simpa using hlarge.trans hcount
  have hηL : K * (η+1/L) ≤ 1/256 := by
    have h := (div_le_iff₀ hLpos).mpr (show K ≤ (1/512)*L by linarith)
    rw [mul_add, mul_one_div]
    linarith only [hKη, h]
  have hR : R ≤ D/64 := by
    have hb := hr B η hBp hη hη'
    change R * L ≤ K*B*(η+1/L) at hb
    have hmul := mul_le_mul_of_nonneg_right hηL (Nat.cast_nonneg B)
    have hcount' := (div_le_iff₀ (by positivity : 0 < 4*L)).mp hcount
    apply le_of_mul_le_mul_right (a := L) _ hLpos
    nlinarith only [hb, hmul, hcount']
  have hH : 1 ≤ H := Nat.le_floor (by simpa using one_le_pow₀ hL (n := 4))
  have herrors := dyadicFloorErrors_le (Nat.cast_nonneg B) hC hLC hcount
  change 5*(H : ℝ)*a^2 + (B : ℝ)^2/H ≤ D^2/8 at herrors
  have hinc := dyadicPairLoss_bound B H η a hB hH (show 0 ≤ a by
    dsimp [a]; positivity) (by
    intro l hl hl₃ hlH
    exact hfibre l hl hl₃ ((Nat.cast_le.mpr hlH).trans (Nat.floor_le (by positivity))))
  change D^2 ≤ G + 2*R*D + D + (5/8 : ℝ)*D^2 + 5*(H : ℝ)*a^2 + (B : ℝ)^2/H at hinc
  have hG : D^2 / 8 ≤ G := by
    nlinarith only [hinc, herrors, mul_le_mul_of_nonneg_right hR (by positivity : 0 ≤ D),
      mul_nonneg (show 0 ≤ D by positivity) (sub_nonneg.mpr hD)]
  have hpower' : 16 * (B : ℝ)^(1-δ/2) ≤ D := hpower.trans hcount
  have hsq := pow_le_pow_left₀ (show 0 ≤ 16*(B : ℝ)^(1-δ/2) by positivity) hpower' 2
  have heq : ((B : ℝ)^(1-δ/2))^2 = (B : ℝ)^(2-δ) := by
    rw [← Real.rpow_natCast ((B : ℝ)^(1-δ/2)) 2, ← Real.rpow_mul (Nat.cast_nonneg B)]
    norm_num
    congr 1
    ring
  rw [mul_pow, heq] at hsq
  change (B : ℝ)^(2-δ) ≤ G
  nlinarith only [hsq, hG, Real.rpow_nonneg (Nat.cast_nonneg B) (2-δ)]

/-- Two lists of `B^(1-o(1))` eligible primes with coprime odd supports
between lists, for every sufficiently large dyadic cutoff. -/
theorem dyadic_good_prime_lists :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/4 ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ B : ℕ in atTop,
      ∃ R ⊆ dyadicEligibleAxes B η, ∃ S ⊆ dyadicEligibleAxes B η,
        (B : ℝ)^(1-ε) ≤ R.card ∧ (B : ℝ)^(1-ε) ≤ S.card ∧
        ∀ p ∈ R, ∀ q ∈ S, ∀ l : ℕ, l.Prime → l ≠ 2 →
          l ∣ p*(p-1) → ¬ l ∣ q*(q-1) := by
  obtain ⟨η, hη, hcut, hp⟩ := dyadicDisjointPairs_supply
  exact ⟨η, hη, hcut, fun _ hε => dyadicPrimeLists_of_pairCount hp hε⟩

end FiniteFourier
end LinearAlgebra
end OAI
