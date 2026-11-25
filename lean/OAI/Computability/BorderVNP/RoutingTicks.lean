import OAI.Computability.BorderVNP.PackedPotential

/-!
# The team tick estimate after physical routing

Equation (8.3) separates public record work, individual wire work, and the
fixed-degree loops on labels and teams. This file checks the final comparison
against the team clock, uniformly in the stretched-exponential batch size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Routing

open Filter TeamScales

/-- The number of labels in the product alphabet of §8.1, with its integer ceiling. -/
noncomputable def labelCount (a : ℕ) (α : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ (3 * α)⌉₊ ^ a

private theorem labels_plus_teams {a R n : ℕ} {α : ℝ} (ha : 1 ≤ a) (hα : 0 ≤ α)
    (hn : 1 ≤ n) (hR : (R : ℝ) ≤ (n : ℝ) ^ (2 * α)) :
    (labelCount a α n : ℝ) + R ≤ ((2 : ℝ)^a + 1) * (n : ℝ) ^ (3 * α * a) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ha' : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hbase := Real.one_le_rpow hn' (by positivity : 0 ≤ 3*α)
  have ceilbound := Nat.ceil_lt_add_one (show 0 ≤ (n : ℝ) ^ (3*α) by positivity)
  have hc : (⌈(n : ℝ) ^ (3*α)⌉₊ : ℝ) ≤ 2 * (n : ℝ) ^ (3*α) := by linarith
  have hl : (labelCount a α n : ℝ) ≤ (2 : ℝ)^a * (n : ℝ) ^ (3*α*a) := by
    simpa only [labelCount, Nat.cast_pow, mul_pow, Real.rpow_mul (zero_le_one.trans hn'), Real.rpow_natCast]
      using (pow_le_pow_left₀ (by positivity) hc a)
  have hr := hR.trans (Real.rpow_le_rpow_of_exponent_le hn'
    (show 2 * α ≤ 3 * α * (a : ℝ) by nlinarith [mul_nonneg hα (sub_nonneg.mpr ha')]))
  linarith

/-- The fixed broadcast fits the stated `rn^0.96` envelope. The first term
accounts for the epoch history and the second for the `d′²` pair declarations.
The final linear term also permits the additional `o(r)` bits of §11. -/
theorem eventually_broadcast_bits (D : ℕ) {α : ℝ} (hα : 0 ≤ α) (hsmall : α < 1/100) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) →
      A * (r * (n : ℝ) ^ (93/100 : ℝ) +
        (labelCount 1 α n : ℝ)^2 * (logWidth r n : ℝ)^D + r) <
        r * (n : ℝ) ^ (24/25 : ℝ) := by
  obtain ⟨ω, hω, hpoly⟩ := exists_polylog_budget D (by norm_num : 0 < (1/100:ℝ))
  refine ⟨ω, hω, ?_⟩
  intro A hA
  have epoch := Packing.eventually_le_rounded_width (by norm_num : (93/100:ℝ) < 24/25)
    (by norm_num) (by norm_num : 0 < (1/4:ℝ)) A
  have pairs := Packing.eventually_le_rounded_width (show 6*α + 1/100 < (24/25:ℝ) by linarith)
    (by norm_num) (by norm_num : 0 < (1/4:ℝ)) (A*9)
  have extra := Packing.eventually_le_rounded_width (by norm_num : (0:ℝ) < 24/25)
    (by norm_num) (by norm_num : 0 < (1/4:ℝ)) A
  filter_upwards [hpoly, epoch, pairs, extra, eventually_ge_atTop 1] with n hp he hg hx hn
  intro r hr hrω
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hpol := hp r hr hrω
  have hlabel := labels_plus_teams (R := 0) (a := 1) le_rfl hα hn
    (by exact_mod_cast Real.rpow_nonneg hn'.le (2*α))
  norm_num only [Nat.cast_zero, add_zero, pow_one, Nat.cast_one, mul_one] at hlabel
  have hpair : (labelCount 1 α n : ℝ)^2 ≤ 9 * (n : ℝ) ^ (6*α) := by
    have hb := pow_le_pow_left₀ (by positivity) hlabel 2
    rw [show 6*α = (3*α) * 2 by ring, Real.rpow_mul hn'.le, Real.rpow_two]
    nlinarith only [hb]
  rw [Real.rpow_zero, mul_one] at hx
  have ht := Nat.floor_le (Real.rpow_nonneg hn'.le (24/25))
  change (width n (24/25) : ℝ) ≤ _ at ht
  calc
    _ ≤ A * (r * (n : ℝ) ^ (93/100:ℝ) + 9 * (n : ℝ) ^ (6*α) * (n : ℝ) ^ (1/100:ℝ) + r) := by
      gcongr
    _ = r * (A * (n : ℝ) ^ (93/100:ℝ)) + A*9 * (n : ℝ) ^ (6*α + 1/100) + r*A := by
      rw [Real.rpow_add hn']
      ring
    _ ≤ r * (1/4 * (width n (24/25):ℝ)) + 1/4 * (width n (24/25):ℝ) +
        r * (1/4 * (width n (24/25):ℝ)) := by gcongr
    _ ≤ (3/4:ℝ) * r * (n : ℝ) ^ (24/25:ℝ) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hr') (Nat.cast_nonneg (width n (24/25))),
        mul_nonneg (zero_le_one.trans hr') (sub_nonneg.mpr ht)]
    _ < _ := by nlinarith only [mul_pos (zero_lt_one.trans_le hr') (Real.rpow_pos_of_pos hn' (24/25))]

/-- The full upper expression in (8.3) is strictly below the processor clock.
`D` is the fixed polylogarithm degree and `A` the fixed implicit constant.
The bound allows all `1 ≤ r ≤ 2^(n^ω)` with a common threshold. -/
theorem eventually_team_ticks (a D : ℕ) (ha : 1 ≤ a) {α ξ : ℝ} (hα : 0 ≤ α)
    (hsmall : α * (a : ℝ) < 1 / 10 ^ 6) (hξ : 0 < ξ) (hξ' : ξ < 1 / 25) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ n : ℕ in atTop, ∀ r R : ℕ, 1 ≤ r →
      (r : ℝ) ≤ 2 ^ ((n : ℝ) ^ ω) → (R : ℝ) ≤ (n : ℝ) ^ (2 * α) →
      A * (r * (n : ℝ) ^ (19 / 20 : ℝ) +
        (exterior ξ r n + ((labelCount a α n : ℝ) + R)^10) * (logWidth r n : ℝ)^D) <
        r * (n : ℝ) ^ (1 - ξ / 2) := by
  obtain ⟨ω, hω, hpoly⟩ := exists_polylog_budget D (show 0 < ξ / 4 by positivity)
  refine ⟨ω, hω, ?_⟩
  intro A hA
  have hbudget : 0 < 1 - ξ/2 := by linarith
  have pub := Packing.eventually_le_rounded_width
    (show (19/20 : ℝ) < 1 - ξ/2 by linarith) hbudget (by norm_num : 0 < (1/4:ℝ)) A
  have wire := Packing.eventually_le_rounded_width
    (show 1 - ξ + ξ/4 < 1 - ξ/2 by linarith) hbudget (by norm_num : 0 < (1/4:ℝ)) A
  have sparse := Packing.eventually_le_rounded_width
    (show (3 * α * (a : ℝ)) * 10 + ξ/4 < 1 - ξ/2 by linarith)
    hbudget (by norm_num : 0 < (1/4:ℝ)) (A * ((2 : ℝ)^a + 1)^10)
  filter_upwards [hpoly, pub, wire, sparse, eventually_ge_atTop 1] with n hp hpub hwire hsparse hn
  intro r R hr hrω hR
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hr' : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hpol := hp r hr hrω
  have exterior_le : (exterior ξ r n : ℝ) ≤ r * (n : ℝ) ^ (1 - ξ) := by
    rw [exterior, Nat.cast_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Nat.floor_le (Real.rpow_nonneg hn'.le _)
  have lab := labels_plus_teams ha hα hn hR
  have hlabels : ((labelCount a α n : ℝ) + R)^10 ≤ ((2 : ℝ)^a + 1)^10 *
      (n : ℝ) ^ (3 * α * a * 10) := by
    simpa only [mul_pow, Real.rpow_mul hn'.le (3 * α * a) (10 : ℝ), Real.rpow_ofNat] using
      (pow_le_pow_left₀ (by positivity) lab 10)
  have ht := Nat.floor_le (Real.rpow_nonneg hn'.le (1 - ξ/2))
  change (width n (1 - ξ/2) : ℝ) ≤ _ at ht
  calc
    _ ≤ A * (r * (n : ℝ) ^ (19 / 20 : ℝ) +
        (r * (n : ℝ) ^ (1 - ξ) + ((2 : ℝ)^a + 1)^10 * (n : ℝ) ^ (3*α*a*10)) *
        (n : ℝ) ^ (ξ / 4)) := by gcongr
    _ = r * (A * (n : ℝ) ^ (19 / 20 : ℝ)) + r * (A * (n : ℝ) ^ (1 - ξ + ξ/4)) +
        (A * ((2 : ℝ)^a + 1)^10) * (n : ℝ) ^ (3*α*a*10 + ξ/4) := by
      rw [Real.rpow_add hn' (1 - ξ) (ξ/4), Real.rpow_add hn' (3*α*a*10) (ξ/4)]
      ring
    _ ≤ r * (1/4 * (width n (1 - ξ/2) : ℝ)) + r * (1/4 * (width n (1 - ξ/2) : ℝ)) +
        1/4 * (width n (1 - ξ/2) : ℝ) := by gcongr
    _ ≤ (3/4 : ℝ) * r * (n : ℝ) ^ (1 - ξ/2) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hr') (Nat.cast_nonneg (width n (1-ξ/2))),
        mul_nonneg (zero_le_one.trans hr') (sub_nonneg.mpr ht)]
    _ < _ := by nlinarith only [mul_pos (zero_lt_one.trans_le hr') (Real.rpow_pos_of_pos hn' (1-ξ/2))]

end Routing

end BorderVNP
end Computability
end OAI
