import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Quantitative transfer through projections and padding

Section 12 selects a source length fitting into every sufficiently large matrix order.
Both the reduction dimension and the cost of degree extraction are polynomial. The
lemma below absorbs these losses into a smaller absolute constant in the exponent.
It also allows polynomial dependence on the candidate size, as needed for
determinantal complexity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

/-- The quantitative lower bound of Theorem 1.1, with base-two logarithms. -/
noncomputable def rate (c : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (c * (Real.logb 2 n) ^ (5 / 4 : ℝ))

/-- Every fixed positive rate eventually strictly dominates every fixed polynomial power. -/
theorem eventually_pow_lt_rate {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (n : ℝ) ^ d < rate c n := by
  have grows : Filter.Tendsto (fun n : ℕ => (Real.logb 2 n) ^ (1 / 4 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (grows.eventually (Filter.eventually_gt_atTop ((d : ℝ) / c)))
  refine ⟨max M 2, ?_⟩
  intro n hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2)
    ((le_max_right M 2).trans hn))
  have hx := Real.logb_pos (by norm_num : (1 : ℝ) < 2) hn'
  have hroot := (div_lt_iff₀ hc).mp (hM n ((le_max_left M 2).trans hn))
  have exp_lt : (d : ℝ) * Real.logb 2 n < c * (Real.logb 2 n) ^ (5 / 4 : ℝ) := by
    rw [show (5 / 4 : ℝ) = 1 / 4 + 1 by norm_num, Real.rpow_add_one hx.ne']
    linarith only [mul_lt_mul_of_pos_right hroot hx]
  calc
    (n : ℝ) ^ d = (2 : ℝ) ^ ((d : ℝ) * Real.logb 2 n) := by
      rw [mul_comm, Real.rpow_mul_natCast (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    _ < rate c n := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) exp_lt

private theorem one_le_rate {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ rate c n := by
  have hx := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  exact Real.one_le_rpow (by norm_num) (mul_nonneg hc (Real.rpow_nonneg hx _))

private theorem rate_add (a b : ℝ) (n : ℕ) : rate (a + b) n = rate a n * rate b n := by
  simp only [rate, add_mul, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

private theorem rate_pow {c : ℝ} {n : ℕ} (f : ℕ) : rate c n ^ f = rate (c * f) n := by
  unfold rate
  rw [← Real.rpow_mul_natCast (by norm_num)]
  ring_nf

private theorem rate_mono_coeff {a b : ℝ} (hab : a ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    rate a n ≤ rate b n := by
  have hx := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hx _))

/-- For any polynomial reindexing bound, all sufficiently large target orders admit a
fitting source order, with the target order also polynomially bounded in the source. -/
theorem exists_fitting_order (A b n₀ : ℕ) :
    ∃ N₀, ∀ N ≥ N₀, ∃ n ≥ max n₀ 2, A * (n + 1) ^ b ≤ N ∧ N ≤ n ^ (2 * (b + 1) + 1) := by
  let length (n : ℕ) := (A + 1) * (n + 1) ^ (b + 1)
  have growth (n : ℕ) : n < length n := by
    refine (Nat.lt_succ_self n).trans_le ?_
    exact (Nat.le_self_pow (Nat.succ_ne_zero b) _).trans
      (Nat.le_mul_of_pos_left _ (Nat.succ_pos A))
  let H := max (max n₀ 2) (A + 1)
  refine ⟨length H, ?_⟩
  intro N hN
  have hHN := (growth H).le.trans hN
  let n := Nat.findGreatest (fun j => length j ≤ N) N
  have hn : H ≤ n := Nat.le_findGreatest hHN hN
  have fits : length n ≤ N := Nat.findGreatest_spec (P := fun j => length j ≤ N) hHN hN
  have succ_large : N < length (n + 1) :=
    lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun j => length j ≤ N)
      (Nat.lt_succ_self n) ((growth n).trans_le fits))
  have hn2 : max n₀ 2 ≤ n := (le_max_left _ _).trans hn
  have ha : A + 1 ≤ n := (le_max_right _ _).trans hn
  refine ⟨n, hn2, ?_, ?_⟩
  · exact (Nat.mul_le_mul (Nat.le_succ A)
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ b))).trans fits
  · have htwo : 2 ≤ n := (le_max_right n₀ 2).trans hn2
    have hsq : n + 1 + 1 ≤ n ^ 2 := by nlinarith [Nat.mul_le_mul htwo htwo]
    calc
      N ≤ length (n + 1) := succ_large.le
      _ ≤ n * (n ^ 2) ^ (b + 1) := Nat.mul_le_mul ha (Nat.pow_le_pow_left hsq _)
      _ = n ^ (2 * (b + 1) + 1) := by rw [pow_succ n (2 * (b + 1)), pow_mul, mul_comm]

/-- Reindexing through a fixed power rescales the coefficient by its exact five-fourths power. -/
theorem rate_reindex {c : ℝ} (hc : 0 ≤ c) {n N k : ℕ}
    (hn : 1 ≤ n) (hN : 1 ≤ N) (hk : 0 < k) (h : N ≤ n ^ k) :
    rate (c / (k : ℝ) ^ (5 / 4 : ℝ)) N ≤ rate c n := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hx := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (show (1 : ℝ) ≤ N by exact_mod_cast hN)
  have hy := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (show (1 : ℝ) ≤ n by exact_mod_cast hn)
  have hlog : Real.logb 2 N ≤ (k : ℝ) * Real.logb 2 n := by
    rw [← Real.logb_pow]
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.zero_lt_of_lt hN)
    exact_mod_cast h
  have hp := Real.rpow_le_rpow hx hlog (by norm_num : (0 : ℝ) ≤ 5 / 4)
  rw [Real.mul_rpow hkr.le hy] at hp
  have hd := Real.rpow_pos_of_pos hkr (5 / 4 : ℝ)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  calc
    c / (k : ℝ) ^ (5 / 4 : ℝ) * (Real.logb 2 N) ^ (5 / 4 : ℝ)
        ≤ c / (k : ℝ) ^ (5 / 4 : ℝ) * ((k : ℝ) ^ (5 / 4 : ℝ) * (Real.logb 2 n) ^ (5 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg hc hd.le)
    _ = _ := by field_simp

/-- A polynomial overhead in dimension and candidate size preserves a positive
rate coefficient. This form applies to the simulation of affine determinants. -/
theorem absorb_polynomial_cost {a : ℝ} (ha : 0 < a) (f : ℕ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ D e : ℕ, ∃ M : ℕ, ∀ N ≥ M, ∀ s : ℕ,
      rate a N ≤ (D * (N + 1) ^ e * (s + 1) ^ f : ℕ) → rate c' N ≤ s := by
  let c' := (a / 2) / (f + 1 : ℝ)
  have hc' : 0 < c' := div_pos (by linarith) (by positivity)
  refine ⟨c', hc', ?_⟩
  intro D e
  obtain ⟨M, hM⟩ := eventually_pow_lt_rate (show 0 < a / 2 by linarith) (1 + 2 * e + f)
  refine ⟨max M (max D 2), ?_⟩
  intro N hN s hs
  have hM' := (le_max_left M (max D 2)).trans hN
  have hD := ((le_max_left D 2).trans (le_max_right M (max D 2))).trans hN
  have htwo := ((le_max_right D 2).trans (le_max_right M (max D 2))).trans hN
  by_contra! small
  have hrate := one_le_rate hc'.le (show 1 ≤ N by omega)
  have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast htwo
  have hDreal : (D : ℝ) ≤ N := by exact_mod_cast hD
  have hsize : (s : ℝ) + 1 ≤ (N : ℝ) * rate c' N := by nlinarith
  have hsquare : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by nlinarith
  have hf : c' * f ≤ a / 2 := by
    have hpos : (0 : ℝ) < f + 1 := by positivity
    dsimp only [c']
    calc
      (a / 2) / (f + 1) * f ≤ (a / 2) / (f + 1) * (f + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hc'.le
      _ = a / 2 := div_mul_cancel₀ _ hpos.ne'
  have hf' : rate c' N ^ f ≤ rate (a / 2) N := by
    rw [rate_pow]
    exact rate_mono_coeff hf (by omega)
  have bound := hs
  push_cast at bound
  have cost :
      (D : ℝ) * ((N : ℝ) + 1) ^ e * ((s : ℝ) + 1) ^ f
        ≤ (N : ℝ) ^ (1 + 2 * e + f) * rate c' N ^ f := by
    calc
      _ ≤ (N : ℝ) * ((N : ℝ) ^ 2) ^ e * ((N : ℝ) * rate c' N) ^ f := by
        gcongr
      _ = _ := by rw [pow_add, pow_add, pow_one, pow_mul, mul_pow]; ring
  have final_lt := mul_lt_mul_of_pos_right (hM N hM') (show 0 < rate c' N ^ f by positivity)
  have : rate a N < rate a N := calc
    rate a N ≤ _ := bound.trans cost
    _ < _ := final_lt
    _ ≤ rate (a / 2) N * rate (a / 2) N := by
      apply mul_le_mul_of_nonneg_left hf'
      exact (one_le_rate (by linarith : 0 ≤ a / 2) (show 1 ≤ N by omega)).trans' (by norm_num)
    _ = rate a N := by rw [← rate_add]; congr 1; ring
  exact (lt_irrefl _ this)
/-- A polynomial reindexing and polynomial costs in both the target dimension and its
candidate size preserve the paper's quantitative lower bound. The new positive constant
is fixed before the input threshold, so it is uniform across characteristics whenever
the reduction bounds and the original constant are uniform. -/
theorem quantitative_all_orders {c : ℝ} (hc : 0 < c) (A b D e f : ℕ) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ n₀ : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ n ≥ max n₀ 2,
      A * (n + 1) ^ b ≤ N ∧ ∀ s : ℕ,
        rate c n ≤ (D * (N + 1) ^ e * (s + 1) ^ f : ℕ) → rate c' N ≤ s := by
  let k := 2 * (b + 1) + 1
  let a := c / (k : ℝ) ^ (5 / 4 : ℝ)
  have hk : 0 < k := Nat.succ_pos _
  have ha : 0 < a := div_pos hc (Real.rpow_pos_of_pos (by exact_mod_cast hk) _)
  obtain ⟨c', hc', hcost⟩ := absorb_polynomial_cost ha f
  refine ⟨c', hc', ?_⟩
  intro n₀
  obtain ⟨L, hL⟩ := exists_fitting_order A b n₀
  obtain ⟨M, hM⟩ := hcost D e
  refine ⟨max L (max M 1), ?_⟩
  intro N hN
  have hL' := (le_max_left L (max M 1)).trans hN
  have hM' := ((le_max_left M 1).trans (le_max_right L (max M 1))).trans hN
  have hN' := ((le_max_right M 1).trans (le_max_right L (max M 1))).trans hN
  obtain ⟨n, hn, fits, hdim⟩ := hL N hL'
  have hcomp : rate a N ≤ rate c n := rate_reindex hc.le (by omega) hN' hk hdim
  exact ⟨n, hn, fits, fun s hs => hM N hM' s (hcomp.trans hs)⟩

end BorderVNP
end Computability
end OAI
