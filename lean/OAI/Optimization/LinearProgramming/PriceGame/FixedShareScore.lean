import OAI.Optimization.LinearProgramming.PriceGame.FixedShare
import OAI.Optimization.LinearProgramming.PriceGame.Majority
import OAI.Optimization.LinearProgramming.PriceGame.MomentLocalCost

/-! The interval score estimate on the actual sequence of outer weights. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open Finset
variable {E : Type*} [DecidableEq E]

def rootTotal (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ) : ℚ :=
  ∑ e ∈ lists t, rootWeights lists scores t e

theorem rootWeights_nonneg (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ) (e : E) :
    0 ≤ rootWeights lists scores t e := by
  induction t generalizing e with
  | zero =>
    simp only [rootWeights, initialWeight]
    split <;> positivity
  | succ t ih =>
    let v := scaledWeight (lists t) (rootWeights lists scores t) (scores t)
    have hv : ∀ j, 0 ≤ v j := scaledWeight_nonneg _ (fun j _ => ih j)
    change 0 ≤ fixedShare (lists (t + 1)) v e
    by_cases he : e ∈ lists (t+1)
    · exact (mul_nonneg (by positivity) (sum_nonneg (fun j _ => hv j))).trans (fixedShare_floor he (hv e))
    · simp [he]

theorem rootWeights_pos_through (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ)
    (hn : ∀ k ≤ t, (lists k).Nonempty) (hg : ∀ k < t, lists k ⊆ lists (k + 1))
    {e : E} (he : e ∈ lists t) : 0 < rootWeights lists scores t e := by
  induction t generalizing e with
  | zero =>
    rw [rootWeights, initialWeight, ite_eq_left he]
    exact inv_pos.mpr (by exact_mod_cast (hn 0 le_rfl).card_pos)
  | succ t ih =>
    let w := rootWeights lists scores t
    let v := scaledWeight (lists t) w (scores t)
    have hv : ∀ j, 0 ≤ v j := scaledWeight_nonneg _ (fun j _ => rootWeights_nonneg _ _ _ j)
    obtain ⟨i, hi⟩ := hn t (Nat.le_succ _)
    have hi' : 0 < v i := by
      dsimp [v]; rw [scaledWeight_of_mem hi]
      exact mul_pos (by positivity) (ih (fun k hk => hn _ (by omega)) (fun k hk => hg _ (by omega)) hi)
    exact fixedShare_pos he (hv e) (sum_pos' (fun j _ => hv j) ⟨i, hg t (Nat.lt_succ_self t) hi, hi'⟩)

theorem rootTotal_pos_through (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ)
    (hn : ∀ k ≤ t, (lists k).Nonempty) (hg : ∀ k < t, lists k ⊆ lists (k+1)) :
    0 < rootTotal lists scores t :=
  sum_pos (fun _ he => rootWeights_pos_through _ _ t hn hg he) (hn t le_rfl)

theorem rootTotal_succ_scaled (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ)
    (hg : lists t ⊆ lists (t+1)) :
    rootTotal lists scores (t+1) = ∑ e ∈ lists t, (2 : ℚ) ^ scores t e * rootWeights lists scores t e :=
  sum_rootUpdate _ _ hg _ _

theorem rootWeights_le_total (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ)
    {e : E} (he : e ∈ lists t) : rootWeights lists scores t e ≤ rootTotal lists scores t :=
  single_le_sum (fun j _ => rootWeights_nonneg _ _ _ j) he

/-- The entrant's share bound also holds for the initial uniform trial. -/
theorem rootWeights_starting_share (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t M : ℕ)
    {e : E} (he : e ∈ lists t) (hM : (lists t).card ≤ M) :
    ((1/64 : ℚ) / M) * rootTotal lists scores t ≤ rootWeights lists scores t e := by
  have hc : 0 < (lists t).card := card_pos.mpr ⟨e, he⟩
  have hcq : (0 : ℚ) < (lists t).card := by exact_mod_cast hc
  have hMq : ((lists t).card : ℚ) ≤ M := by exact_mod_cast hM
  have hfrac : (1 / 64 : ℚ) / M ≤ (1 / 64 : ℚ) / (lists t).card :=
    div_le_div_of_nonneg_left (by norm_num) hcq hMq
  cases t with
  | zero =>
    rw [rootTotal, show (∑ i ∈ lists 0, rootWeights lists scores 0 i) = 1 from sum_initialWeight _ ⟨_, he⟩,
      mul_one, rootWeights, initialWeight, ite_eq_left he, ← one_div]
    exact hfrac.trans (div_le_div_of_nonneg_right (by norm_num) hcq.le)
  | succ t =>
    let v := scaledWeight (lists t) (rootWeights lists scores t) (scores t)
    have hv : ∀ j, 0 ≤ v j := scaledWeight_nonneg _ (fun j _ => rootWeights_nonneg _ _ _ j)
    have hT : rootTotal lists scores (t+1) = ∑ j ∈ lists (t+1), v j := sum_fixedShare _ _
    rw [hT]
    exact (mul_le_mul_of_nonneg_right hfrac (sum_nonneg (fun j _ => hv j))).trans (fixedShare_floor he (hv e))

theorem rootWeights_keep (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ) {e : E}
    (he : e ∈ lists t) (he' : e ∈ lists (t+1)) :
    (1 - 1/64) * (rootWeights lists scores t e * (2 : ℚ) ^ scores t e) ≤
      rootWeights lists scores (t+1) e := by
  let v := scaledWeight (lists t) (rootWeights lists scores t) (scores t)
  have hv : ∀ j, 0 ≤ v j := scaledWeight_nonneg _ (fun j _ => rootWeights_nonneg _ _ _ j)
  have h := fixedShare_retained he' (fun j _ => hv j)
  change (1 - 1/64) * v e ≤ rootWeights lists scores (t+1) e at h
  simpa only [v, scaledWeight_of_mem he, mul_comm (rootWeights lists scores t e)] using h

/-- Charges to a persistent expert on an arbitrary contiguous interval. Nonemptiness
and persistence of the lists are needed only through the last update under consideration. -/
theorem rootWeights_interval_score_bound (lists : ℕ → Finset E) (scores : ℕ → E → ℕ)
    (a n M : ℕ) (e : E) {τ : ℝ}
    (hn : ∀ k ≤ a+n, (lists k).Nonempty) (hg : ∀ k < a+n, lists k ⊆ lists (k+1))
    (he : e ∈ lists a) (hM : (lists a).card ≤ M)
    (hmoment : ∀ i < n,
      (∑ j ∈ lists (a+i), (rootWeights lists scores (a+i) j : ℝ) * (2 : ℝ) ^ scores (a+i) j)
        ≤ (2 : ℝ) ^ τ * (rootTotal lists scores (a+i) : ℝ)) :
    ∑ i ∈ range n, (scores (a+i) e : ℝ) ≤
      (τ + Real.logb 2 (1 / (1 - (1/64 : ℝ)))) * n + Real.logb 2 ((M : ℝ) / (1/64 : ℝ)) := by
  have hmem (i : ℕ) (hi : i ≤ n) : e ∈ lists (a+i) := by
    induction i with
    | zero => simpa using he
    | succ i ih => exact hg (a+i) (by omega) (ih (by omega))
  let time (i : ℕ) := a + min i n
  have htime (i : ℕ) : time i ≤ a+n := Nat.add_le_add_left (min_le_right _ _) _
  have hMe : 0 < M := lt_of_lt_of_le (card_pos.mpr ⟨_,he⟩) hM
  apply interval_score_bound n (fun i => scores (a+i) e)
    (fun i => (rootWeights lists scores (time i) e : ℝ))
    (fun i => (rootTotal lists scores (time i) : ℝ)) (by norm_num) (by norm_num) (by exact_mod_cast hMe)
  · intro i
    exact_mod_cast rootWeights_pos_through lists scores (time i)
      (fun k hk => hn _ (hk.trans (htime _))) (fun k hk => hg _ (hk.trans_le (htime _)))
      (hmem (min i n) (min_le_right ..))
  · intro i
    exact_mod_cast rootTotal_pos_through lists scores (time i)
      (fun k hk => hn _ (hk.trans (htime _))) (fun k hk => hg _ (hk.trans_le (htime _)))
  · have h := (Rat.cast_le (K := ℝ)).mpr (rootWeights_starting_share lists scores a M he hM)
    push_cast at h
    simpa only [time, zero_min, Nat.add_zero] using h
  · simpa only [time, min_self] using
      (Rat.cast_le (K := ℝ)).mpr (rootWeights_le_total lists scores (a+n) (hmem n le_rfl))
  · intro i hi
    have h := (Rat.cast_le (K := ℝ)).mpr (rootWeights_keep lists scores (a+i) (hmem i hi.le) (hmem (i+1) hi))
    push_cast at h
    simpa only [time, min_eq_left (Nat.le_of_lt hi), min_eq_left (Nat.succ_le_of_lt hi), Nat.add_assoc] using h
  · intro i hi
    simp only [time, min_eq_left (Nat.le_of_lt hi), min_eq_left (Nat.succ_le_of_lt hi)]
    rw [show a + (i + 1) = a + i + 1 by omega, rootTotal_succ_scaled lists scores (a+i) (hg _ (by omega))]
    push_cast
    simpa only [mul_comm (rootWeights lists scores (a + i) _ : ℝ)] using hmoment i hi

theorem rootTotal_le_rpow (lists : ℕ → Finset E) (scores : ℕ → E → ℕ) (t : ℕ) {τ : ℝ}
    (h0 : (lists 0).Nonempty) (hg : ∀ i < t, lists i ⊆ lists (i+1))
    (hmoment : ∀ i < t, (∑ e ∈ lists i, (rootWeights lists scores i e : ℝ) * (2 : ℝ)^scores i e) ≤
      (2 : ℝ)^τ * (rootTotal lists scores i : ℝ)) :
    (rootTotal lists scores t : ℝ) ≤ (2 : ℝ) ^ (τ * t) := by
  induction t with
  | zero =>
    rw [show rootTotal lists scores 0 = 1 from sum_initialWeight _ h0]
    simp
  | succ t ih =>
    have hprev := ih (fun i hi => hg _ (by omega)) (fun i hi => hmoment _ (by omega))
    calc
      _ ≤ (2 : ℝ)^τ * (rootTotal lists scores t : ℝ) := by
        rw [rootTotal_succ_scaled lists scores t (hg _ (by omega))]
        push_cast
        simpa only [mul_comm (rootWeights lists scores t _ : ℝ)] using hmoment t (Nat.lt_succ_self _)
      _ ≤ (2 : ℝ)^τ * 2^(τ * t) := mul_le_mul_of_nonneg_left hprev (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num)]; congr 1; push_cast; ring

theorem outerDenominator_pos (m : ℕ → ℕ) (t : ℕ) (hm : ∀ i ≤ t, 0 < m i) :
    0 < outerDenominator m t := by
  induction t with
  | zero => exact hm _ le_rfl
  | succ t ih =>
    exact Nat.mul_pos (Nat.mul_pos (ih fun i hi => hm _ (by omega)) (by decide)) (hm _ le_rfl)

/-- Bounds for both integers in the reduced encoding of an actual incoming expert weight. -/
theorem rootWeights_encoding_bounds (lists : ℕ → Finset E) (scores : ℕ → E → ℕ)
    (b t : ℕ) (e : E) {τ : ℝ} (hτ : τ ≤ 1)
    (hn : ∀ i ≤ t, (lists i).Nonempty) (hg : ∀ i < t, lists i ⊆ lists (i+1))
    (hcap : ∀ i ≤ t, (lists i).card ≤ 2 ^ b) (he : e ∈ lists t)
    (hmoment : ∀ i < t, (∑ j ∈ lists i, (rootWeights lists scores i j : ℝ) * (2 : ℝ)^scores i j) ≤
      (2 : ℝ)^τ * (rootTotal lists scores i : ℝ)) :
    (rootWeights lists scores t e).den ≤ 2 ^ (b + (6 + b) * t) ∧
    (rootWeights lists scores t e).num.natAbs ≤ 2 ^ (t + b + (6 + b) * t) := by
  let D := outerDenominator (fun i => (lists i).card) t
  have hD : 0 < D := outerDenominator_pos _ _ (fun i hi => (hn _ hi).card_pos)
  have hDb : D ≤ 2 ^ (b + (6+b)*t) := outerDenominator_le_two_pow _ _ _ hcap
  have hDd := rootWeights_den_dvd lists scores t e
  have hT := rootTotal_le_rpow lists scores t (hn _ (Nat.zero_le _)) hg hmoment
  have hpow : (2 : ℝ) ^ (τ*t) ≤ 2 ^ (t : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by simpa using mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg t : (0 : ℝ) ≤ t))
  rw [Real.rpow_natCast] at hpow
  have hq : (rootWeights lists scores t e : ℝ) ≤ (2 : ℝ)^t :=
    ((Rat.cast_le (K := ℝ)).mpr (rootWeights_le_total lists scores t he)).trans (hT.trans hpow)
  have hq' : |rootWeights lists scores t e| ≤ ((2 ^ t : ℕ) : ℚ) := by
    rw [abs_of_nonneg (rootWeights_nonneg ..)]
    exact_mod_cast hq
  have hnum := Moment.rat_num_abs_le_of_den_dvd _ (2^t) D hD hq' hDd
  refine ⟨(Nat.le_of_dvd hD hDd).trans hDb, hnum.trans ?_⟩
  rw [Nat.add_assoc, pow_add]
  exact Nat.mul_le_mul_left _ hDb

end PriceGame
end LinearProgramming
end Optimization
end OAI
