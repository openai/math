import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! # The common working order and extension capacity

The least common multiple of the outer working lengths and short radix orders
fits within the number of complementary coordinate settings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Filter Finset

section

variable {ι : Type*}

/-- Common order of the transforms on the axes and their short radix blocks. -/
def workingOrder (A : Finset ι) (b : ι → ℕ) (D : Finset ℕ) (s : ℕ → ℕ) : ℕ :=
  Nat.lcm (A.lcm b) (D.lcm s)

theorem axis_dvd_workingOrder {A : Finset ι} {b : ι → ℕ} {i : ι} (hi : i ∈ A)
    (D : Finset ℕ) (s : ℕ → ℕ) : b i ∣ workingOrder A b D s :=
  (dvd_lcm hi).trans (Nat.dvd_lcm_left ..)

theorem short_dvd_workingOrder (A : Finset ι) (b : ι → ℕ) {D : Finset ℕ} {s : ℕ → ℕ}
    {d : ℕ} (hd : d ∈ D) : s d ∣ workingOrder A b D s :=
  (dvd_lcm hd).trans (Nat.dvd_lcm_right ..)

theorem workingOrder_cast_ne_zero (K : Type*) [Field K]
    {A : Finset ι} {b : ι → ℕ} {D : Finset ℕ} {s : ℕ → ℕ}
    (hb : ∀ i ∈ A, (b i : K) ≠ 0) (hs : ∀ d ∈ D, (s d : K) ≠ 0) :
    (workingOrder A b D s : K) ≠ 0 := by
  have hdiv : workingOrder A b D s ∣ (A.prod b) * D.prod s :=
    (Nat.lcm_dvd_mul _ _).trans (Nat.mul_dvd_mul (A.lcm_dvd_prod b) (D.lcm_dvd_prod s))
  obtain ⟨k, hk⟩ := hdiv
  intro hz
  have hc := congrArg (fun n : ℕ ↦ (n : K)) hk
  simp only [Nat.cast_mul, Nat.cast_prod, hz, zero_mul] at hc
  exact mul_ne_zero (prod_ne_zero_iff.mpr hb) (prod_ne_zero_iff.mpr hs) hc

private theorem axis_prod_le {A : Finset ι} {a b : ι → ℕ}
    (ha : ∀ i ∈ A, 2 ≤ a i) (hb : ∀ i ∈ A, b i < 6 * a i) :
    A.prod b ≤ (A.prod a) ^ 4 := by
  rw [← prod_pow]
  apply prod_le_prod (fun i hi ↦ ?_)
  have h := ha i hi
  have hc : 8 ≤ (a i) ^ 3 := by
    exact pow_le_pow_left' h 3
  calc
    b i ≤ 6 * a i := (hb i hi).le
    _ ≤ (a i) ^ 3 * a i := Nat.mul_le_mul_right _ (by omega)
    _ = (a i) ^ 4 := (pow_succ _ _).symm

private theorem short_lcm_le {D : Finset ℕ} {s j : ℕ → ℕ} {t ℓ : ℕ} (ht : 0 < t)
    (hℓ : 0 < ℓ) (hj : ∀ d ∈ D, s d = ℓ ^ j d)
    (hs : ∀ d ∈ D, s d < 6 * d) (hd : ∀ d ∈ D, d ≤ 3 * t ^ 2) :
    D.lcm s ≤ 18 * t ^ 2 := by
  rcases D.eq_empty_or_nonempty with rfl | hD
  · rw [Finset.lcm_empty]
    exact show 0 < 18 * t ^ 2 by positivity
  obtain ⟨d, hmem, hmax⟩ := D.exists_max_image j hD
  have hx : D.lcm s ∣ s d := by
    apply Finset.lcm_dvd
    intro x h
    rw [hj x h, hj d hmem]
    exact pow_dvd_pow _ (hmax x h)
  have hpos : 0 < s d := by rw [hj d hmem]; positivity
  exact (Nat.le_of_dvd hpos hx).trans <| by linarith [hs d hmem, hd d hmem]

/-- The common order has at most one factor of size `18t²` from the radix
powers. The product of all outer lengths contributes at most `B⁴`. -/
theorem workingOrder_le {A : Finset ι} {a b : ι → ℕ} {D : Finset ℕ} {s j : ℕ → ℕ}
    {t ℓ : ℕ} (ht : 0 < t) (hℓ : 0 < ℓ)
    (ha : ∀ i ∈ A, 2 ≤ a i) (hb : ∀ i ∈ A, b i < 6 * a i)
    (hd : ∀ d ∈ D, d ≤ 3 * t ^ 2) (hj : ∀ d ∈ D, s d = ℓ ^ j d)
    (hs : ∀ d ∈ D, s d < 6 * d) :
    workingOrder A b D s ≤ 18 * t ^ 2 * (A.prod a) ^ 4 := by
  by_cases hzero : ∃ i ∈ A, b i = 0
  · simp [workingOrder, Finset.lcm_eq_zero_iff.mpr hzero]
  have hp : 0 < A.prod b := prod_pos (fun i hi ↦ Nat.pos_of_ne_zero (fun h ↦ hzero ⟨i, hi, h⟩))
  have hsp : 0 < D.lcm s := by
    apply Nat.pos_of_ne_zero
    rw [ne_eq, Finset.lcm_eq_zero_iff]
    rintro ⟨d, hm, hz⟩
    rw [hj d hm] at hz
    exact (pow_ne_zero _ hℓ.ne') hz
  calc
    workingOrder A b D s ≤ A.prod b * D.lcm s :=
      Nat.le_of_dvd (Nat.mul_pos hp hsp) ((Nat.lcm_dvd_mul _ _).trans
        (Nat.mul_dvd_mul (A.lcm_dvd_prod b) dvd_rfl))
    _ ≤ (A.prod a) ^ 4 * (18 * t ^ 2) :=
      Nat.mul_le_mul (axis_prod_le ha hb) (short_lcm_le ht hℓ hj hs hd)
    _ = _ := Nat.mul_comm _ _

/-- The common-order bound fits in the `N/B` complementary coordinate settings
uniformly for every block volume satisfying the paper's `B¹² ≤ N`. -/
theorem eventually_workingCapacity_le :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 0 < B → B ^ 12 ≤ N →
      18 * (Nat.clog 2 N) ^ 2 * B ^ 4 ≤ N / B := by
  have hclog : Tendsto (Nat.clog 2) atTop atTop := by
    refine tendsto_atTop.2 fun k ↦ ?_
    filter_upwards [eventually_gt_atTop (2 ^ k : ℕ)] with n hn
    exact ((Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 hn).le
  have hg := (tendsto_pow_const_div_const_pow_of_one_lt 4 (by norm_num : (1 : ℝ) < 2)
    ).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 648)
  filter_upwards [hclog.eventually hg, eventually_gt_atTop (1 : ℕ)] with N hN hN₁ B hB hvol
  let t := Nat.clog 2 N
  have ht := Nat.clog_pos (by decide : 1 < 2) hN₁
  have hg' : 648 * t ^ 4 ≤ 2 ^ t := by
    have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ t)).mp hN
    exact_mod_cast (show (648 : ℝ) * t ^ 4 ≤ 2 ^ t by linarith)
  have hpow : 2 ^ (t - 1) < N := Nat.pow_lt_of_lt_clog (show t - 1 < t by dsimp [t]; omega)
  have hsq : (18 * t ^ 2) ^ 2 ≤ N := by
    have heq : 2 ^ t = 2 ^ (t - 1) * 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ t by exact ht)]
      rw [pow_succ]
    rw [heq] at hg'
    nlinarith only [hg', hpow]
  have hBpow : B ^ 10 ≤ N := (Nat.pow_le_pow_right hB (by decide : 10 ≤ 12)).trans hvol
  apply (Nat.le_div_iff_mul_le hB).2
  change 18 * t ^ 2 * B ^ 4 * B ≤ N
  apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
  calc
    (18 * t ^ 2 * B ^ 4 * B) ^ 2 = (18 * t ^ 2) ^ 2 * B ^ 10 := by ring
    _ ≤ N * N := Nat.mul_le_mul hsq hBpow
    _ = N ^ 2 := (sq _).symm

end

end FiniteFourier
end LinearAlgebra
end OAI
