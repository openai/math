import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace Count

open Finset

/-- Number of indices strictly before `t` at which a feature received a charge. -/
def chargeCount (charged : ℕ → Bool) (t : ℕ) : ℕ :=
  ((range t).filter fun k => charged k).card

private theorem chargeCount_succ (charged : ℕ → Bool) (t : ℕ) :
    chargeCount charged (t + 1) = chargeCount charged t + if charged t then 1 else 0 := by
  unfold chargeCount
  by_cases h : charged t <;> simp [range_add_one, filter_insert, h]

/-- Section 7. A charged integer width is at least one. Between charges its
range can only contract. This bounds the number of charges even if every
threshold is chosen using all preceding replies. -/
theorem charge_count_le_log (p R T : ℕ) (hR : 0 < R)
    (width : ℕ → ℕ) (charged : ℕ → Bool) (hstart : width 0 ≤ 2 * R)
    (hmono : ∀ t < T, width (t + 1) ≤ width t)
    (hpos : ∀ t < T, charged t = true → 0 < width t)
    (hshrink : ∀ t < T, charged t = true →
      (width (t + 1) : ℝ) ≤ (1 - 1 / ((p : ℝ) + 1)) * width t) :
    (chargeCount charged T : ℝ) ≤ 1 + ((p : ℝ) + 1) * Real.log (2 * R) := by
  let s : ℝ := p + 1
  let M : ℝ := 2 * R
  have hs : 0 < s := by dsimp [s]; positivity
  have hM : 1 ≤ M := by dsimp [M]; exact_mod_cast (show 1 ≤ 2 * R by omega)
  have hcoef : 1 - 1 / s ≤ Real.exp (-(1 / s)) := by
    simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(1 / s))
  have inv (n : ℕ) (hn : n ≤ T) :
      (width n : ℝ) ≤ M * Real.exp (-((chargeCount charged n : ℝ) / s)) ∧
      (chargeCount charged n : ℝ) ≤ 1 + s * Real.log M := by
    induction n with
    | zero =>
      simp only [chargeCount, range_zero, filter_empty, card_empty, Nat.cast_zero,
        zero_div, neg_zero, Real.exp_zero, mul_one]
      exact ⟨by dsimp [M]; exact_mod_cast hstart,
        by have := Real.log_nonneg hM; positivity⟩
    | succ n ih =>
      obtain ⟨hw, hc⟩ := ih (by omega)
      have hnt : n < T := by omega
      by_cases he : charged n = true
      · have he1 : (1 : ℝ) ≤ width n := by exact_mod_cast hpos n hnt he
        have hE : Real.exp ((chargeCount charged n : ℝ) / s) ≤ M := by
          have h := he1.trans hw
          rwa [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul] at h
        have hlog := (Real.le_log_iff_exp_le (lt_of_lt_of_le one_pos hM)).2 hE
        have hbudget := (div_le_iff₀ hs).mp hlog
        simp only [chargeCount_succ, he, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        refine ⟨?_, by linarith⟩
        calc
          (width (n+1) : ℝ)
              ≤ (1 - 1 / s) * width n := hshrink n hnt he
          _ ≤ Real.exp (-(1 / s)) * width n :=
              mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
          _ ≤ Real.exp (-(1 / s)) * (M * Real.exp (-((chargeCount charged n : ℝ) / s))) :=
              mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
          _ = M * Real.exp (-(((chargeCount charged n : ℝ) + 1) / s)) := by
              rw [add_div, neg_add, Real.exp_add]; ring
      · have hf : charged n = false := Bool.eq_false_iff.mpr he
        simp only [chargeCount_succ, hf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        exact ⟨(Nat.cast_le.mpr (hmono n hnt)).trans hw, hc⟩
  exact (inv T le_rfl).2

private theorem sum_chargeCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (feature : ℕ → ι) (t : ℕ) :
    ∑ i, chargeCount (fun k => decide (feature k = i)) t = t := by
  induction t with
  | zero => simp [chargeCount]
  | succ t ih =>
    simp [chargeCount_succ, sum_add_distrib, ih]

/-- Charge each exceptional trial to one feature of one skeleton, using the
product of the skeleton and feature types for `ι` if appropriate. -/
theorem exceptional_trials_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (R T : ℕ) (hR : 0 < R)
    (feature : ℕ → ι) (width : ι → ℕ → ℕ)
    (hstart : ∀ i, width i 0 ≤ 2 * R)
    (hmono : ∀ i t, t < T → width i (t + 1) ≤ width i t)
    (hpos : ∀ t < T, 0 < width (feature t) t)
    (hshrink : ∀ t < T, (width (feature t) (t + 1) : ℝ) ≤
      (1 - 1 / ((p (feature t) : ℝ) + 1)) * width (feature t) t) :
    (T : ℝ) ≤ ∑ i, (1 + ((p i : ℝ) + 1) * Real.log (2 * R)) := by
  have h i := charge_count_le_log (p i) R T hR (width i)
    (fun t => decide (feature t = i)) (hstart i) (hmono i)
    (by intro t ht e; simpa [← of_decide_eq_true e] using hpos t ht)
    (by intro t ht e; simpa [← of_decide_eq_true e] using hshrink t ht)
  calc
    (T : ℝ) = ∑ i, (chargeCount (fun t => decide (feature t = i)) T : ℝ) := by
      exact_mod_cast (sum_chargeCount feature T).symm
    _ ≤ _ := sum_le_sum fun i _ => h i

end Count
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
