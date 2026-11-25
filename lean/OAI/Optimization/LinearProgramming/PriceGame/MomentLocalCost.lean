import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

open Finset

private theorem sum_den_dvd {I : Type*} (s : Finset I) (f : I → ℚ) (Q : ℕ)
    (hf : ∀ i ∈ s, (f i).den ∣ Q) : (∑ i ∈ s, f i).den ∣ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (hf i (mem_insert_self _ _)) (ih (fun j hj => hf j (mem_insert_of_mem hj))))

/-- When flows use units of `1/Q`, one multiplicative local update only introduces
the fixed denominator of the learning rate. -/
theorem local_update_den_dvd {I : Type*} [Fintype I] (wt η : ℚ) (f : I → ℚ)
    (signed : I → ℤ) (Q : ℕ) (hw : wt.den ∣ Q)
    (hf : ∀ i, (wt * f i).den ∣ Q) :
    (wt * (1 + η * ∑ i, f i * (signed i : ℚ))).den ∣ Q * η.den := by
  have hg : (∑ i, (wt * f i) * (signed i : ℚ)).den ∣ Q := by
    apply sum_den_dvd
    intro i _
    apply (Rat.mul_den_dvd _ _).trans
    simpa using hf i
  have eqn : wt * (1 + η * ∑ i, f i * (signed i : ℚ)) =
      wt + η * ∑ i, (wt * f i) * (signed i : ℚ) := by
    simp only [mul_add, mul_one, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [eqn]
  refine (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd ?_ ?_)
  · exact hw.trans (Nat.dvd_mul_right _ _)
  · apply (Rat.mul_den_dvd _ _).trans
    rw [Nat.mul_comm Q]
    exact Nat.mul_dvd_mul_left _ hg

/-- Denominators through an entire node's sequence of probes. -/
theorem local_run_den_dvd {E I : Type*} [Fintype I] (Q : ℕ) (η : ℚ)
    (weight : ℕ → E → ℚ) (f : ℕ → E → I → ℚ) (signed : ℕ → E → I → ℤ) (r : ℕ)
    (hinit : ∀ e, (weight 0 e).den ∣ Q)
    (hstep : ∀ t < r, ∀ e, weight (t + 1) e = weight t e *
      (1 + η * ∑ i, f t e i * (signed t e i : ℚ)))
    (hflow : ∀ t < r, ∀ e i, (weight t e * f t e i).den ∣ Q * η.den ^ t) :
    ∀ e, (weight r e).den ∣ Q * η.den ^ r := by
  induction r with
  | zero => simpa using hinit
  | succ r ih =>
    intro e
    have ht := ih (fun t h => hstep t (Nat.lt_succ_of_lt h)) (fun t h => hflow t (Nat.lt_succ_of_lt h))
    rw [hstep r (Nat.lt_succ_self _) e, pow_succ, ← Nat.mul_assoc]
    exact local_update_den_dvd _ _ _ _ _ (ht e) (hflow r (Nat.lt_succ_self _) e)

/-- A positive incoming local weight remains positive, and at most doubles in a probe. -/
theorem local_run_weight_bounds (η : ℚ) (w g : ℕ → ℚ) (r : ℕ)
    (hη : 0 ≤ η) (hsmall : η ≤ 1 / 2) (hw : 0 < w 0)
    (hstep : ∀ t < r, w (t + 1) = w t * (1 + η * g t))
    (hg : ∀ t < r, |g t| ≤ 1) :
    0 < w r ∧ w r ≤ (2 : ℚ) ^ r * w 0 := by
  induction r with
  | zero => simpa using hw
  | succ r ih =>
    have hprev := ih (fun t ht ↦ hstep t (Nat.lt_succ_of_lt ht))
      (fun t ht ↦ hg t (Nat.lt_succ_of_lt ht))
    have hb := abs_le.mp (hg r (Nat.lt_succ_self r))
    have hlo := mul_le_mul_of_nonneg_left hb.1 hη
    have hhi := mul_le_mul_of_nonneg_left hb.2 hη
    have hp : 0 < 1 + η * g r := by linarith
    have hup : 1 + η * g r ≤ 2 := by linarith
    rw [hstep r (Nat.lt_succ_self _)]
    refine ⟨mul_pos hprev.1 hp, ?_⟩
    calc
      _ ≤ ((2 : ℚ) ^ r * w 0) * 2 := mul_le_mul hprev.2 hup hp.le (by positivity)
      _ = 2 ^ (r + 1) * w 0 := by ring

/-- Bounding the magnitude and giving a common denominator bounds the reduced numerator. -/
theorem rat_num_abs_le_of_den_dvd (q : ℚ) (B Q : ℕ) (hQ : 0 < Q)
    (hb : |q| ≤ (B : ℚ)) (hd : q.den ∣ Q) : q.num.natAbs ≤ B * Q := by
  have hdq : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hnum : (q.num : ℚ) = q * q.den := (div_eq_iff hdq).mp q.num_div_den
  have hsize : (q.den : ℚ) ≤ (Q : ℚ) := by exact_mod_cast Nat.le_of_dvd hQ hd
  have habs : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, hnum, abs_mul, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℚ) ≤ q.den)]
  have hbound : (q.num.natAbs : ℚ) ≤ (B : ℚ) * (Q : ℚ) := by
    rw [habs]
    exact mul_le_mul hb hsize (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact_mod_cast hbound

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
