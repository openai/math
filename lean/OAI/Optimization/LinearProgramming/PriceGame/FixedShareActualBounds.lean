import OAI.Optimization.LinearProgramming.PriceGame.Campaign

/-! Arithmetic bounds on the rational weights stored in the growing outer population. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign
open Finset Learning

def populationDenominator {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ) : ℕ :=
  outerDenominator (fun j => (population R out j).ids.card) t

theorem populationDenominator_pos {N : ℕ} (anchor : Fin N) (R : ℕ)
    (out : ℕ → RoundResult N) (t : ℕ) : 0 < populationDenominator R out t :=
  outerDenominator_pos _ _ (fun k _ => (population_nonempty anchor R out k).card_pos)

theorem population_weights_lookup {N : ℕ} (p : Population N) (i : Fin p.experts.length) :
    populationWeights p i = p.weight i.val := by
  simp [populationWeights, Population.weight, Population.lookup, i.isLt]

theorem population_weight_den_dvd {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ)
    (i : Fin (population R out t).experts.length) :
    (populationWeights (population R out t) i).den ∣ populationDenominator R out t := by
  rw [population_weights_lookup]
  exact (replay_weight_eq (Pool.batch N R) out t) ▸
    (rootWeights_den_dvd (fun j => (population R out j).ids) (fun j => (out j).scores) t i.val)

theorem population_card_mono {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) :
    Monotone (fun j => (population R out j).ids.card) :=
  monotone_nat_of_le_succ fun j => Finset.card_le_card (replay_ids_grow (Pool.batch N R) _ out j)

theorem populationDenominator_le {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t b : ℕ)
    (hcap : (population R out t).experts.length ≤ 2^b) :
    populationDenominator R out t ≤ 2^(b+(6+b)*t) := by
  apply outerDenominator_le_two_pow
  intro j hj
  apply (population_card_mono R out hj).trans
  simpa only [Population.ids, card_range] using hcap

theorem moment_tau_le_one : Moment.tau ≤ 1 := by
  have hp : (1 : ℝ) ≤ 2 ^ 272 := one_le_pow₀ (by norm_num)
  calc
    Moment.tau = (1 / (2 : ℝ)^272) / 8 := rfl
    _ ≤ (1 / (1 : ℝ)) / 8 := div_le_div_of_nonneg_right
      (one_div_le_one_div_of_le zero_lt_one hp) (by norm_num)
    _ ≤ 1 := by norm_num

/-- A pointwise bound on the stored total for any admissible sequence of score moments. -/
theorem population_total_le_of_moments {N : ℕ} (anchor : Fin N) (R : ℕ)
    (out : ℕ → RoundResult N) (t : ℕ)
    (hmoment : ∀ k < t,
      (∑ j ∈ (population R out k).ids, ((population R out k).weight j : ℝ) * (2 : ℝ) ^ (out k).scores j)
        ≤ (2 : ℝ) ^ Moment.tau * ∑ j ∈ (population R out k).ids, ((population R out k).weight j : ℝ)) :
    (∑ i ∈ (population R out t).ids, (population R out t).weight i) ≤ (2 : ℚ)^t := by
  let lists := fun j => (population R out j).ids
  let scores := fun j => (out j).scores
  have hw (k : ℕ) : (population R out k).weight = rootWeights lists scores k := replay_weight_eq ..
  have hm (i : ℕ) (hi : i < t) :
      ∑ j ∈ lists i, (rootWeights lists scores i j : ℝ) * 2^scores i j ≤
      (2 : ℝ)^Moment.tau * (rootTotal lists scores i : ℝ) := by
    unfold rootTotal
    rw [← hw]
    push_cast
    exact hmoment i hi
  have hT := rootTotal_le_rpow lists scores t (population_nonempty anchor R out 0)
    (fun j _ => replay_ids_grow _ _ _ j) hm
  have hτt : Moment.tau * (t : ℝ) ≤ t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right moment_tau_le_one (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hτt
  rw [Real.rpow_natCast] at hpow
  have hb : rootTotal lists scores t ≤ (2 : ℚ)^t := by exact_mod_cast hT.trans hpow
  rw [hw]
  exact hb

theorem population_total_le {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val)) (t : ℕ) (ht : t ≤ T) :
    (∑ i ∈ (population R out t).ids, (population R out t).weight i) ≤ (2 : ℚ)^t := by
  apply population_total_le_of_moments anchor
  intro i hi
  exact round_moment h markets _ _ ((validRun_iff_steps ..).mp hr i (by omega))

/-- Each current entry is a summand of the incoming total. -/
theorem population_weight_le_sum {N : ℕ} (R : ℕ) (out : ℕ → RoundResult N) (t : ℕ)
    (i : Fin (population R out t).experts.length) :
    populationWeights (population R out t) i ≤ ∑ j ∈ (population R out t).ids, (population R out t).weight j := by
  have hw := replay_weight_eq (Pool.batch N R) out t
  rw [population_weights_lookup, hw]
  exact rootWeights_le_total _ _ t (show i.val ∈ (population R out t).ids from mem_range.mpr i.isLt)

theorem population_weight_le {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val)) (t : ℕ) (ht : t ≤ T)
    (i : Fin (population R out t).experts.length) :
    populationWeights (population R out t) i ≤ (2 : ℚ)^t := by
  exact (population_weight_le_sum R out t i).trans (population_total_le h markets out hr t ht)

/-- The two reduced integers and the underlying common denominator on an actual
incoming root state. The parameter `b` can be the current catalogue length's bit length. -/
theorem population_encoding_bounds {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (markets : AvailableMarkets N) (out : ℕ → RoundResult N) {T : ℕ}
    (hr : ValidRun (Pool.batch N R) (runRound R markets) h T
      (Population.start (Pool.batch N R)) (fun i => out i.val)) (t b : ℕ) (ht : t ≤ T)
    (hcap : (population R out t).experts.length ≤ 2^b) (i : Fin (population R out t).experts.length) :
    let q := populationWeights (population R out t) i
    let D := populationDenominator R out t
    0 < D ∧ D ≤ 2^(b+(6+b)*t) ∧ q.den ∣ D ∧ 0 ≤ q ∧ q ≤ (2 : ℚ)^t ∧
      q.den ≤ 2^(b+(6+b)*t) ∧ q.num.natAbs ≤ 2^(t+b+(6+b)*t) := by
  let q := populationWeights (population R out t) i
  let D := populationDenominator R out t
  have hD : 0 < D := populationDenominator_pos anchor R out t
  have hcap' := populationDenominator_le R out t b hcap
  have hd : q.den ∣ D := population_weight_den_dvd R out t i
  have hq : q ≤ (2 : ℚ)^t := population_weight_le h markets out hr t ht i
  have hq₀ : 0 ≤ q := (population R out t).nonnegative i
  have hq' : |q| ≤ ((2 ^ t : ℕ) : ℚ) := by rw [abs_of_nonneg hq₀]; exact_mod_cast hq
  have hnum := Moment.rat_num_abs_le_of_den_dvd q (2^t) D hD hq' hd
  refine ⟨hD, hcap', hd, hq₀, hq, (Nat.le_of_dvd hD hd).trans hcap', hnum.trans ?_⟩
  rw [Nat.add_assoc, pow_add]
  exact Nat.mul_le_mul_left _ hcap'

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
