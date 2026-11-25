import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The rounding step of the exponential-moment induction in Section 5. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

open Finset

/-- Return the rounded score for an expert with mean `H`. -/
noncomputable def roundedScore (C σ H : ℝ) : ℕ := ⌈C * max 0 (H - σ / 2)⌉₊

/-- On implementation data the score is computed entirely by rational arithmetic. -/
def rationalScore (C σ H : ℚ) : ℕ := ⌈C * max 0 (H - σ / 2)⌉₊

@[simp] theorem roundedScore_ratCast (C σ H : ℚ) :
    roundedScore C σ H = rationalScore C σ H := by
  unfold roundedScore rationalScore
  rw [← Int.ceil_toNat, ← Int.ceil_toNat]
  norm_cast

theorem roundedScore_eq_zero {C σ H : ℝ} (h : H ≤ σ / 2) : roundedScore C σ H = 0 := by
  simp [roundedScore, max_eq_left (sub_nonpos.mpr h)]

theorem roundedScore_lower {C σ H : ℝ} (hC : 0 ≤ C) :
    C * (H - σ / 2) ≤ roundedScore C σ H :=
  (mul_le_mul_of_nonneg_left (le_max_right _ _) hC).trans (Nat.le_ceil _)

theorem roundedScore_pointwise {C σ K H : ℝ} (hC : 0 ≤ C) (hK : C ≤ K) :
    (2 : ℝ) ^ roundedScore C σ H ≤
      1 + (2 * (2 : ℝ) ^ (-(K * σ / 2))) * (2 : ℝ) ^ (K * H) := by
  by_cases h : H ≤ σ / 2
  · rw [roundedScore_eq_zero h, pow_zero]
    exact le_add_of_nonneg_right (by positivity)
  have hp : 0 ≤ H - σ / 2 := sub_nonneg.mpr (le_of_lt (lt_of_not_ge h))
  have hround : (roundedScore C σ H : ℝ) ≤ 1 + K * (H - σ / 2) := by
    rw [roundedScore, max_eq_right hp]
    apply (Nat.ceil_lt_add_one (mul_nonneg hC hp)).le.trans
    linarith [mul_le_mul_of_nonneg_right hK hp]
  rw [← Real.rpow_natCast]
  refine (Real.rpow_le_rpow_of_exponent_le (by norm_num) hround).trans ?_
  have he : 1 + K * (H - σ / 2) = (1 + -(K * σ / 2)) + K * H := by ring
  rw [he, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one]
  linarith

/-- The incoming exponential estimate survives thresholding and rounding. -/
theorem roundedScore_moment {E : Type*} [Fintype E] (w H : E → ℝ) {C σ τ K : ℝ}
    (hw : ∀ e, 0 ≤ w e) (hC : 0 ≤ C) (hσ : 0 ≤ σ) (hK : C ≤ K)
    (hbranch : 1 + 2 * (2 : ℝ) ^ (-K * σ / 4) ≤ (2 : ℝ) ^ τ)
    (havg : (∑ e, w e * (2 : ℝ) ^ (K * H e)) ≤ (2 : ℝ) ^ (K * σ / 8) * ∑ e, w e) :
    (∑ e, w e * (2 : ℝ) ^ roundedScore C σ (H e)) ≤ (2 : ℝ) ^ τ * ∑ e, w e := by
  let a : ℝ := 2 * (2 : ℝ) ^ (-(K * σ / 2))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hcoeff : 1 + a * (2 : ℝ) ^ (K * σ / 8) ≤ (2 : ℝ) ^ τ := by
    apply le_trans _ hbranch
    dsimp [a]
    rw [mul_assoc, ← Real.rpow_add (by norm_num)]
    gcongr <;> nlinarith [mul_nonneg (hC.trans hK) hσ]
  calc
    (∑ e, w e * (2 : ℝ) ^ roundedScore C σ (H e)) ≤
        ∑ e, (w e + a * (w e * (2 : ℝ) ^ (K * H e))) := by
          apply sum_le_sum
          intro e he
          calc
            _ ≤ w e * (1 + a * (2 : ℝ) ^ (K * H e)) :=
              mul_le_mul_of_nonneg_left (roundedScore_pointwise hC hK) (hw e)
            _ = _ := by ring
    _ = (∑ e, w e) + a * ∑ e, w e * (2 : ℝ) ^ (K * H e) := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ (∑ e, w e) + a * ((2 : ℝ) ^ (K * σ / 8) * ∑ e, w e) := by gcongr
    _ = (1 + a * (2 : ℝ) ^ (K * σ / 8)) * ∑ e, w e := by ring
    _ ≤ (2 : ℝ) ^ τ * ∑ e, w e :=
      mul_le_mul_of_nonneg_right hcoeff (sum_nonneg (fun e _ => hw e))

/-- Deeper experts are updated only by the nonnegative integer scores of their children. -/
def deepWeight {E : Type*} (initial : E → ℝ) (score : ℕ → E → ℕ) (t : ℕ) (e : E) : ℝ :=
  initial e * 2 ^ ∑ j ∈ range t, score j e

@[simp] theorem deepWeight_zero {E : Type*} (w : E → ℝ) (s : ℕ → E → ℕ) (e : E) :
    deepWeight w s 0 e = w e := by simp [deepWeight]

theorem deepWeight_succ {E : Type*} (w : E → ℝ) (s : ℕ → E → ℕ) (t : ℕ) (e : E) :
    deepWeight w s (t + 1) e = deepWeight w s t e * 2 ^ s t e := by
  simp [deepWeight, sum_range_succ, pow_add, mul_assoc]

theorem deepWeight_nonneg {E : Type*} {w : E → ℝ} (s : ℕ → E → ℕ) (t : ℕ) (e : E)
    (hw : 0 ≤ w e) : 0 ≤ deepWeight w s t e := by unfold deepWeight; positivity

theorem cumulative_deep_moment {E : Type*} [Fintype E] (w : E → ℝ) (s : ℕ → E → ℕ)
    (r : ℕ) (τ : ℝ)
    (h : ∀ t < r, (∑ e, deepWeight w s t e * 2 ^ s t e) ≤
      (2 : ℝ) ^ τ * ∑ e, deepWeight w s t e) :
    (∑ e, deepWeight w s r e) ≤ (2 : ℝ) ^ ((r : ℝ) * τ) * ∑ e, w e := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ = ∑ e, deepWeight w s r e * 2 ^ s r e := by simp only [deepWeight_succ]
      _ ≤ (2 : ℝ) ^ τ * ∑ e, deepWeight w s r e := h _ (Nat.lt_succ_self _)
      _ ≤ (2 : ℝ) ^ τ * ((2 : ℝ) ^ ((r : ℝ) * τ) * ∑ e, w e) :=
        mul_le_mul_of_nonneg_left (ih fun t ht => h t (Nat.lt_succ_of_lt ht)) (by positivity)
      _ = _ := by
        rw [← mul_assoc, ← Real.rpow_add (by norm_num)]
        push_cast
        ring_nf

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
