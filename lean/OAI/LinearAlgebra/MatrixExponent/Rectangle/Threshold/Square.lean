import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Surplus
import Mathlib.Data.Nat.Sqrt

/-! # Square output of side s and inner width proportional to its square root -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

private theorem half_side (s : ℕ) : side (s * s) (1 / 2) = s := by
  rw [side, Nat.cast_mul, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by positivity), Nat.ceil_natCast]

private theorem half_width (s : ℕ) (a : ℝ) :
    Threshold.width (s * s) (1 / 2) (1 / 2) a = ⌈a * Real.sqrt s⌉₊ := by
  rw [Threshold.width, Nat.cast_mul, Real.rpow_mul (by positivity),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by positivity)]

/-- Restrict the scaled threshold to the subsequence of square sizes.
Away from this subsequence use arbitrary ordinary products. -/
theorem square_threshold {K : ℕ → Type*} [∀ n, Field (K n)] {a : ℝ}
    (ha : 0 < a) (ha' : a ≤ Real.sqrt (Real.exp 1))
    (hrig : ∀ n, Rigidity (K n)) (hsq : ∀ n, MatrixExponent.omega (K n) = 9 / 4)
    (w : ∀ s, Fin s → Fin s → Fin ⌈a * Real.sqrt s⌉₊ → K s)
    (hw : ∀ s i j k, w s i j k ≠ 0) (r : ℕ → ℕ) (hr : ∀ s, BorderRankLE (w s) (r s))
    {L : ℝ} (hL : L < Real.exp (-2) * a ^ 4) :
    ∀ᶠ s : ℕ in atTop, L < ((r s : ℝ) - (s : ℝ) ^ 2) * Real.log ((s : ℝ) ^ 2) / (s : ℝ) ^ 2 := by
  have he (n : ℕ) : ∃ (v : Fin (side n (1 / 2)) → Fin (side n (1 / 2)) →
      Fin (Threshold.width n (1 / 2) (1 / 2) a) → K (Nat.sqrt n)) (p : ℕ),
      (∀ i j k, v i j k ≠ 0) ∧ BorderRankLE v p ∧ (∀ s : ℕ, n = s * s → p = r s) := by
    by_cases hn : ∃ s, n = s * s
    · obtain ⟨s, rfl⟩ := hn
      rw [half_side, half_width, Nat.sqrt_eq]
      refine ⟨w s, r s, hw s, hr s, fun t ht => ?_⟩
      simpa using congrArg (fun n => r (Nat.sqrt n)) ht
    · let v := ordinary (K (Nat.sqrt n)) (side n (1 / 2)) (side n (1 / 2)) (Threshold.width n (1 / 2) (1 / 2) a)
      exact ⟨v, rankW v, fun _ _ _ => one_ne_zero, (rankW_spec v).border, fun s h => (hn ⟨s, h⟩).elim⟩
  choose v p hv hp heq using he
  have hopt := Threshold.square_optimum ha ha'
  have hh := scaled_border_surplus (by norm_num) (by norm_num) (by norm_num) ha
    (fun n => hrig (Nat.sqrt n)) (fun n => hsq (Nat.sqrt n)) v hv p hp (L := L) (by
      rw [show (Real.log a) / ((1 / 2 : ℝ) * (1 / 2)) = 4 * Real.log a by ring, min_self,
        div_self (by norm_num : (1 / 2 : ℝ) ≠ 0), hopt]
      exact hL)
  obtain ⟨n, hn⟩ := eventually_atTop.mp hh
  filter_upwards [eventually_ge_atTop n] with s hs
  simpa only [normalized, half_side, heq _ s rfl, pow_two] using hn (s * s) (hs.trans (Nat.le_mul_self s))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
