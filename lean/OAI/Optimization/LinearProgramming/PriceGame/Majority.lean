import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import OAI.Optimization.LinearProgramming.PriceGame.Model

/-! Fixed-share weights and the final majority argument in Section 7. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

open Finset

/-- Introducing new experts with zero old weight preserves the total under the fixed-share rule. -/
theorem fixedShare_total {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (α : ℝ) :
    ∑ i ∈ s, ((1 - α) * w i + (α / s.card) * ∑ e ∈ s, w e) = ∑ i ∈ s, w i := by
  have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

theorem fixedShare_lower_bounds {α m w total : ℝ} (ha : 0 ≤ α) (ha₁ : α ≤ 1)
    (hm : 0 < m) (hw : 0 ≤ w) (hT : 0 ≤ total) :
    (1 - α) * w ≤ (1 - α) * w + α / m * total ∧
    α / m * total ≤ (1 - α) * w + α / m * total := by
  exact ⟨le_add_of_nonneg_right (mul_nonneg (div_nonneg ha hm.le) hT),
    le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr ha₁) hw)⟩

/-- A persistent expert's cumulative score on an interval. The old weight is retained through
fixed sharing, and the total grows at most by the moment factor at each trial. -/
theorem interval_score_bound
    (n : ℕ) (score : ℕ → ℕ) (w total : ℕ → ℝ) {α m τ : ℝ}
    (ha : 0 < α) (ha₁ : α < 1) (hm : 0 < m)
    (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 < total i)
    (hstart : α / m * total 0 ≤ w 0) (hend : w n ≤ total n)
    (hkeep : ∀ i < n, (1 - α) * (w i * 2 ^ score i) ≤ w (i + 1))
    (hgrow : ∀ i < n, (total (i + 1)) ≤ (2 : ℝ) ^ τ * total i) :
    ∑ i ∈ range n, (score i : ℝ) ≤
      (τ + Real.logb 2 (1 / (1 - α))) * n + Real.logb 2 (m / α) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hr : 0 < 1 - α := sub_pos.mpr ha₁
  let φ i := Real.logb 2 (w i) - Real.logb 2 (total i)
  have step (i : ℕ) (hi : i < n) :
      (score i : ℝ) ≤ φ (i + 1) - φ i + (τ - Real.logb 2 (1 - α)) := by
    have hwstep := Real.logb_le_logb_of_le h2
      (mul_pos hr (mul_pos (hw i) (pow_pos (by norm_num : (0 : ℝ) < 2) _))) (hkeep i hi)
    have htstep := Real.logb_le_logb_of_le h2 (ht (i + 1)) (hgrow i hi)
    rw [Real.logb_mul hr.ne' (mul_pos (hw i) (pow_pos (by norm_num : (0 : ℝ) < 2) _)).ne',
      Real.logb_mul (hw i).ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one h2,
      mul_one] at hwstep
    rw [Real.logb_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) τ).ne' (ht i).ne',
      Real.logb_rpow (by norm_num) (by norm_num)] at htstep
    dsimp [φ]
    linarith
  have partial_bound (k : ℕ) (hk : k ≤ n) :
      ∑ i ∈ range k, (score i : ℝ) ≤ φ k - φ 0 + (τ - Real.logb 2 (1 - α)) * k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ, Nat.cast_succ]
      linarith [ih (by omega), step k (by omega)]
  have hs := Real.logb_le_logb_of_le h2 (mul_pos (div_pos ha hm) (ht 0)) hstart
  rw [Real.logb_mul (div_pos ha hm).ne' (ht 0).ne', Real.logb_div ha.ne' hm.ne'] at hs
  have he := Real.logb_le_logb_of_le h2 (hw n) hend
  have hb := partial_bound n le_rfl
  dsimp [φ] at hb
  rw [one_div, Real.logb_inv, Real.logb_div hm.ne' ha.ne']
  linarith

/-- On a good interval the same distribution of selected experts charges every failed trial. -/
theorem charged_interval_bound {ι κ : Type*} (trials : Finset ι) (experts : Finset κ)
    (failed : ι → Bool) (score : ι → κ → ℝ) (weight : κ → ℝ) {budget : ℝ}
    (hb : 0 ≤ budget) (hw : ∀ e ∈ experts, 0 ≤ weight e)
    (hmass : ∑ e ∈ experts, weight e ≤ 1)
    (hcharge : ∀ t ∈ trials, (if failed t then (1 : ℝ) else 0) ≤
      ∑ e ∈ experts, weight e * score t e)
    (hcaps : ∀ e ∈ experts, ∑ t ∈ trials, score t e ≤ budget) :
    ∑ t ∈ trials, (if failed t then (1 : ℝ) else 0) ≤ budget := by
  calc
    _ ≤ ∑ t ∈ trials, ∑ e ∈ experts, weight e * score t e := sum_le_sum hcharge
    _ = ∑ e ∈ experts, weight e * ∑ t ∈ trials, score t e := by
      rw [sum_comm]
      simp_rw [mul_sum]
    _ ≤ ∑ e ∈ experts, weight e * budget :=
      sum_le_sum fun e he => mul_le_mul_of_nonneg_left (hcaps e he) (hw e he)
    _ = (∑ e ∈ experts, weight e) * budget := (sum_mul ..).symm
    _ ≤ budget := by simpa using mul_le_mul_of_nonneg_right hmass hb

/-- A successful root separator votes correctly at the known active anchor. -/
theorem anchor_vote {N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor) (x : Fin N → ℚ)
    (succeeds : ∀ i ∈ h.active, (R + 1 : ℚ) - (h.cost i : ℕ) ≤ h.signedPrice (x i)) :
    decide (0 < x anchor) = h.positive := by
  have hc := (h.cost anchor).isLt
  have hc' : ((h.cost anchor : ℕ) : ℚ) ≤ R := by exact_mod_cast Nat.le_of_lt_succ hc
  have hx := succeeds anchor h.anchor_mem
  cases p : h.positive
  · simp [Hidden.signedPrice, p] at hx
    simp [show ¬ 0 < x anchor by linarith]
  · simp [Hidden.signedPrice, p] at hx
    simp [show 0 < x anchor by linarith]

/-- The strict positive-anchor majority used at the end of the algorithm. -/
def priceMajority {T : ℕ} (price : Fin T → ℚ) : Bool :=
  decide (T < 2 * (univ.filter fun t => 0 < price t).card)

theorem majority_of_few_failures {T N R : ℕ} {anchor : Fin N} (h : Hidden N R anchor)
    (x : Fin T → Fin N → ℚ) (failed : Finset (Fin T))
    (hsucceeds : ∀ t ∉ failed, ∀ i ∈ h.active,
      (R + 1 : ℚ) - (h.cost i : ℕ) ≤ h.signedPrice (x t i))
    (hsmall : 2 * failed.card < T) :
    priceMajority (fun t => x t anchor) = h.positive := by
  classical
  let yes := univ.filter fun t : Fin T => 0 < x t anchor
  let no := univ.filter fun t : Fin T => ¬ 0 < x t anchor
  have hp : yes.card + no.card = T := by
    simpa [yes, no] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin T))) (fun t => 0 < x t anchor))
  have vote (t : Fin T) (ht : t ∉ failed) := anchor_vote h (x t) (hsucceeds t ht)
  cases p : h.positive with
  | false =>
    have hsub : yes ⊆ failed := by
      intro t hty
      by_contra hf
      have := vote t hf
      simp [p, (mem_filter.mp hty).2] at this
    have := card_le_card hsub
    change decide (T < 2 * yes.card) = false
    simp [show ¬ T < 2 * yes.card by omega]
  | true =>
    have hsub : no ⊆ failed := by
      intro t htn
      by_contra hf
      have := vote t hf
      simp [p, (mem_filter.mp htn).2] at this
    have := card_le_card hsub
    change decide (T < 2 * yes.card) = true
    simp [show T < 2 * yes.card by omega]

/-- A register-computable exponent gap for the trial count. It depends only on the
two fixed dimension exponents in the catalogue and exception estimates. -/
def trialGap (e c : ℕ) : ℕ :=
  let L := 4 * (13 + 2*c*(e+2)) + 16*c + 1
  L + L

theorem trialGap_spec (e c : ℕ) :
    4 * (13 + 2 * c * (e + 1 + trialGap e c + 1)) < 2 ^ trialGap e c := by
  let A := 4 * (13 + 2 * c * (e + 2))
  let L := A + 16 * c + 1
  have hA : A ≤ L := by dsimp [L]; omega
  have hB : 16 * c ≤ L := by dsimp [L]; omega
  have hp : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self (n := L)
  change 4 * (13 + 2*c*(e + 1 + (L+L) + 1)) < 2^(L+L)
  calc
    4 * (13 + 2 * c * (e + 1 + (L + L) + 1)) = A + (16 * c) * L := by dsimp [A]; ring
    _ ≤ L + L * L := Nat.add_le_add hA (Nat.mul_le_mul_right L hB)
    _ < (L + 1) * (L + 1) := by nlinarith
    _ ≤ 2 ^ L * 2 ^ L := Nat.mul_le_mul hp hp
    _ = 2 ^ (L + L) := (pow_add _ _ _).symm

theorem exists_trial_exponent (e c : ℕ) :
    ∃ j : ℕ, 4 * (13 + 2 * c * (e + 1 + j + 1)) < 2 ^ j :=
  ⟨trialGap e c, trialGap_spec e c⟩

theorem trial_overhead_bound {X e c j E m : ℕ} (hX : 2 ≤ X) (hm : 1 ≤ m)
    (hE : E ≤ X ^ e) (hsize : m ≤ (X * X ^ (e + 1 + j)) ^ c)
    (hexp : 4 * (13 + 2 * c * (e + 1 + j + 1)) < 2 ^ j) :
    (E : ℝ) + (E + 1 : ℝ) * Real.logb 2 (64 * (m : ℝ)) <
      (X : ℝ) ^ (e + 1 + j) / 4 := by
  let k := e + 1 + j
  let C := c * (k + 1)
  have hx : 1 ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
  have hx₀ : 0 < (X : ℝ) := by linarith
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hl : Real.logb 2 X ≤ (X : ℝ) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num) hx₀).mpr
    rw [Real.rpow_natCast]
    exact_mod_cast (Nat.lt_two_pow_self (n := X)).le
  have hsize' : (m : ℝ) ≤ ((X : ℝ) * X ^ k) ^ c := by exact_mod_cast hsize
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hm₀ hsize'
  rw [Real.logb_pow, Real.logb_mul hx₀.ne' (pow_pos hx₀ k).ne', Real.logb_pow] at hlog
  have hlog' : Real.logb 2 (64 * (m : ℝ)) ≤ 6 + C * (X : ℝ) := by
    have h64 : Real.logb 2 64 = 6 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
      norm_num
    rw [Real.logb_mul (by norm_num) hm₀.ne', h64]
    have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ (C : ℝ) by positivity)
    dsimp [C] at hh ⊢
    push_cast at hh ⊢
    nlinarith
  have hE' : (E : ℝ) ≤ (X : ℝ) ^ e := by exact_mod_cast hE
  have hU : 1 ≤ (X : ℝ) ^ e := one_le_pow₀ hx
  have hconst : (4 : ℝ) * (13 + 2 * (C : ℝ)) < (X : ℝ) ^ j := by
    have h' : 4 * (13 + 2 * C) < X ^ j :=
      lt_of_lt_of_le (by simpa [C, k, Nat.mul_assoc] using hexp) (Nat.pow_le_pow_left hX j)
    exact_mod_cast h'
  have hE₁ : (E : ℝ) + 1 ≤ 2 * (X : ℝ)^e := by linarith
  have hbudget : (E : ℝ) + (E + 1 : ℝ) * Real.logb 2 (64 * (m : ℝ))
      ≤ (13 + 2 * (C : ℝ)) * ((X : ℝ) ^ e * X) := by
    calc
      _ ≤ (X : ℝ) ^ e + (E + 1 : ℝ) * (6 + C * (X : ℝ)) :=
        add_le_add hE' (mul_le_mul_of_nonneg_left hlog' (by positivity))
      _ ≤ (X : ℝ) ^ e + (2 * (X : ℝ) ^ e) * (6 + C * (X : ℝ)) :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hE₁ (by positivity))
      _ ≤ (13 + 2 * (C : ℝ)) * ((X : ℝ) ^ e * X) := by
        nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ (X : ℝ)^e by positivity)]
  have hstrict := mul_lt_mul_of_pos_right hconst (show 0 < (X : ℝ)^e * X by positivity)
  rw [pow_add, pow_succ]
  nlinarith

/-- Fixed share costs less than one eighth of a unit of average score. -/
theorem source_gamma_bound :
    1 / (2 : ℝ)^275 + Real.logb 2 (1 / (1 - (1 / 64 : ℝ))) < 1 / 8 := by
  have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : 0 < (64 / 63 : ℝ) ^ (16 : ℕ))
    (by norm_num : (64 / 63 : ℝ) ^ (16 : ℕ) < 2)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h
  norm_num at h
  rw [show 1 / (1 - (1 / 64 : ℝ)) = 64 / 63 by norm_num]
  have small : 1 / (2 : ℝ)^275 ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le (by norm_num)
    calc (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
         _ ≤ 2 ^ (275 : ℕ) := pow_le_pow_right₀ (by norm_num) (by norm_num)
  calc
    _ ≤ 1 / 16 + Real.logb 2 (64 / 63) := add_le_add small le_rfl
    _ < 1 / 8 := by linarith only [h]

/-- Summing the interval caps, including the exceptional trials. A tag of `none` denotes
an exceptional trial; there are at most `E + 1` good intervals, including empty ones. -/
theorem total_failures_bound {T E : ℕ} (failed : Finset (Fin T))
    (tag : Fin T → Option (Fin (E + 1))) {γ overhead : ℝ} (hγ : 0 ≤ γ)
    (hexceptions : (univ.filter fun t => tag t = none).card ≤ E)
    (hblock : ∀ b : Fin (E + 1),
      ∑ t ∈ univ.filter (fun t => tag t = some b), (if t ∈ failed then (1 : ℝ) else 0) ≤
      γ * (univ.filter (fun t => tag t = some b)).card + overhead) :
    (failed.card : ℝ) ≤ E + γ * T + (E + 1 : ℕ) * overhead := by
  classical
  let count (a : Option (Fin (E + 1))) : ℝ :=
    ∑ t ∈ univ.filter (fun t => tag t = a), if t ∈ failed then (1 : ℝ) else 0
  let size (a : Option (Fin (E + 1))) : ℝ := (univ.filter (fun t => tag t = a)).card
  have hcount : ∑ a, count a = failed.card := by
    dsimp [count]
    rw [sum_fiberwise]
    simp
  have hsize : ∑ a, size a = T := by
    have hs := sum_fiberwise (univ : Finset (Fin T)) tag (fun _ => (1 : ℝ))
    simpa [size] using hs
  rw [Fintype.sum_option] at hcount hsize
  have hbad : count none ≤ E := by
    calc
      _ ≤ ∑ _t ∈ univ.filter (fun t => tag t = none), (1 : ℝ) := by
        apply sum_le_sum
        intro t ht
        split_ifs <;> norm_num
      _ ≤ E := by simpa using (show ((univ.filter (fun t => tag t = none)).card : ℝ) ≤ E by exact_mod_cast hexceptions)
  have hgood : ∑ j : Fin (E + 1), count (some j) ≤
      γ * (∑ j : Fin (E + 1), size (some j)) + (E + 1 : ℕ) * overhead := by
    calc
      _ ≤ ∑ j : Fin (E+1), (γ * size (some j) + overhead) := sum_le_sum (fun j _ => hblock j)
      _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp
  have hno : 0 ≤ size none := by dsimp [size]; positivity
  have hgoodsize : ∑ j : Fin (E + 1), size (some j) ≤ T := by linarith
  linarith [mul_le_mul_of_nonneg_left hgoodsize hγ]

/-- The polynomial trial choice turns the exceptional/charging estimate into a correct final vote. -/
theorem polynomial_trials_vote {X e c j E m N R : ℕ} {anchor : Fin N}
    (h : Hidden N R anchor) (hX : 2 ≤ X) (hm : 1 ≤ m)
    (hE : E ≤ X ^ e) (hsize : m ≤ (X * X ^ (e + 1 + j)) ^ c)
    (hexp : 4 * (13 + 2 * c * (e + 1 + j + 1)) < 2 ^ j)
    (x : Fin (X ^ (e + 1 + j)) → Fin N → ℚ) (failed : Finset (Fin (X ^ (e + 1 + j))))
    (tag : Fin (X ^ (e + 1 + j)) → Option (Fin (E + 1)))
    (hexceptions : (univ.filter fun t => tag t = none).card ≤ E)
    (hsucceeds : ∀ t ∉ failed, ∀ i ∈ h.active,
      (R + 1 : ℚ) - (h.cost i : ℕ) ≤ h.signedPrice (x t i))
    (hblock : ∀ b : Fin (E + 1),
      ∑ t ∈ univ.filter (fun t => tag t = some b), (if t ∈ failed then (1 : ℝ) else 0) ≤
      (1/8 : ℝ) * (univ.filter (fun t => tag t = some b)).card + Real.logb 2 (64 * (m : ℝ))) :
    priceMajority (fun t => x t anchor) = h.positive := by
  apply majority_of_few_failures h x failed hsucceeds
  have htot := total_failures_bound failed tag (by norm_num) hexceptions hblock
  have hover := trial_overhead_bound hX hm hE hsize hexp
  push_cast at htot
  have hpos : 0 < (X : ℝ) ^ (e + 1 + j) := pow_pos (by exact_mod_cast (show 0 < X by omega)) _
  exact_mod_cast (show 2 * (failed.card : ℝ) < (X : ℝ) ^ (e+1+j) by linarith)

end PriceGame
end LinearProgramming
end Optimization
end OAI
