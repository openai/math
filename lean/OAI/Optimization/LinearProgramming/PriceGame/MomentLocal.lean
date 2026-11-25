import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

/-- Gain on allocated coordinates. Mass on the outside option contributes zero. -/
def allocationGain {E I : Type*} [Fintype I] (f : E → I → ℝ)
    (u : E → ℝ) (z : I → ℝ) (e : E) : ℝ := ∑ i, f e i * u e * z i

theorem allocationGain_abs_le_one {E I : Type*} [Fintype I] {f : E → I → ℝ}
    {u : E → ℝ} {z : I → ℝ} (e : E) (hf : ∀ i, 0 ≤ f e i) (hu : |u e| = 1)
    (hz : ∀ i, |z i| = 1) (hmass : ∑ i, f e i ≤ 1) :
    |allocationGain f u z e| ≤ 1 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa [abs_mul, abs_of_nonneg (hf _), hu, hz] using hmass

theorem allocationGain_balanced {E I : Type*} [Fintype E] [Fintype I]
    (L : E → ℝ) (f : E → I → ℝ) (u : E → ℝ) (z : I → ℝ)
    (hbal : ∀ i, ∑ e, L e * u e * f e i = 0) :
    ∑ e, L e * allocationGain f u z e = 0 := by
  simp only [allocationGain, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  calc
    ∑ e, L e * (f e i * u e * z i) = (∑ e, L e * u e * f e i) * z i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = 0 := by rw [hbal i, zero_mul]

/-- Weight immediately before probe `r`, numbering probes from zero. -/
def localWeight {E : Type*} (η : ℝ) (initial : E → ℝ) (gain : ℕ → E → ℝ)
    (r : ℕ) (e : E) : ℝ := initial e * ∏ t ∈ Finset.range r, (1 + η * gain t e)

@[simp] theorem localWeight_zero {E : Type*} (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (e : E) : localWeight η initial gain 0 e = initial e := by
  simp [localWeight]

@[simp] theorem localWeight_succ {E : Type*} (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (r : ℕ) (e : E) :
    localWeight η initial gain (r + 1) e = localWeight η initial gain r e * (1 + η * gain r e) := by
  simp [localWeight, Finset.prod_range_succ, mul_assoc]

theorem localWeight_sum_eq {E : Type*} [Fintype E] (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (r : ℕ)
    (hbal : ∀ t < r, ∑ e, localWeight η initial gain t e * gain t e = 0) :
    ∑ e, localWeight η initial gain r e = ∑ e, initial e := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih fun t ht ↦ hbal t (Nat.lt_trans ht (Nat.lt_succ_self _))
    calc
      ∑ e, localWeight η initial gain (r + 1) e =
          ∑ e, (localWeight η initial gain r e + η * (localWeight η initial gain r e * gain r e)) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [localWeight_succ]; ring
      _ = ∑ e, initial e := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbal r (Nat.lt_succ_self r), hprev]
        ring

/-- The lower Taylor estimate for the logarithm on the half-unit interval. -/
theorem sub_sq_le_log_one_add (x : ℝ) (hx : |x| ≤ 1 / 2) :
    x - x ^ 2 ≤ Real.log (1 + x) := by
  have hnorm : ‖(x : ℂ)‖ = |x| := by simp
  have hpos : 0 < 1 + x := by linarith [(abs_le.mp hx).1]
  have h := Complex.norm_log_one_add_sub_self_le (z := (x : ℂ))
    (by rw [hnorm]; linarith)
  have hre : (1 + (x : ℂ)) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
  rw [hre, ← Complex.ofReal_log hpos.le, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, hnorm] at h
  have hden : 0 < 1 - |x| := by linarith
  have hinv : (1 - |x|)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hden]
    linarith
  have hsq := mul_le_mul_of_nonneg_left hinv (sq_nonneg |x|)
  rw [sq_abs] at hsq h
  linarith [neg_le_abs (Real.log (1 + x) - x)]

theorem exp_gain_sub_sq_le_update {η g : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hg : |g| ≤ 1) : Real.exp (η * g - η ^ 2) ≤ 1 + η * g := by
  have habs : |η * g| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    simpa using mul_le_mul_of_nonneg_left hg hη
  have hsq : (η * g) ^ 2 ≤ η ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (η * g)) habs 2)
  have hlog := sub_sq_le_log_one_add _ (habs.trans hη')
  have hpos : 0 < 1 + η * g := by linarith [(abs_le.mp (habs.trans hη')).1]
  exact (Real.exp_le_exp.mpr (by linarith : η * g - η ^ 2 ≤ Real.log (1 + η * g))).trans_eq
    (Real.exp_log hpos)

theorem local_exponential_estimate {E : Type*} [Fintype E]
    (η : ℝ) (initial : E → ℝ) (gain : ℕ → E → ℝ) (r : ℕ)
    (hinit : ∀ e, 0 ≤ initial e) (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hg : ∀ t < r, ∀ e, |gain t e| ≤ 1)
    (hbal : ∀ t < r, ∑ e, localWeight η initial gain t e * gain t e = 0) :
    (∑ e, initial e * Real.exp (η * ∑ t ∈ Finset.range r, gain t e)) ≤
      Real.exp (η ^ 2 * r) * ∑ e, initial e := by
  have hpoint (e : E) :
      Real.exp (η * ∑ t ∈ Finset.range r, gain t e - η ^ 2 * r) ≤
        ∏ t ∈ Finset.range r, (1 + η * gain t e) := by
    calc
      _ = ∏ t ∈ Finset.range r, Real.exp (η * gain t e - η ^ 2) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [mul_comm]
      _ ≤ _ := Finset.prod_le_prod₀ (fun t _ ↦ (Real.exp_pos _).le)
        (fun t ht ↦ exp_gain_sub_sq_le_update hη hη' (hg t (Finset.mem_range.mp ht) e))
  rw [← localWeight_sum_eq η initial gain r hbal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hs :
      Real.exp (η * ∑ t ∈ Finset.range r, gain t e) =
        Real.exp (η ^ 2 * r) * Real.exp (η * ∑ t ∈ Finset.range r, gain t e - η ^ 2 * r) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hs, localWeight, mul_left_comm (initial e)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpoint e) (hinit e))
    (Real.exp_pos _).le

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
