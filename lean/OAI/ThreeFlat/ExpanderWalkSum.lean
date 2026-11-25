import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI
/-! # Summing the estimates along a nonlinear random walk -/

namespace ThreeFlat.Expander

open Finset

/-- The first half of the walk controls the displacement sum. Every power
in the second half also controls the accumulated increments in the first. -/
theorem walk_scalar_bound {k : ℕ} (hk : 0 < k) {E D b : ℕ → ℝ} {W γ : ℝ}
    (hγ : 0 ≤ γ) (hE : ∀ g, 0 ≤ E g) (hD : ∀ g, 0 ≤ D g)
    (hp : ∀ h, D h + ∑ g ∈ range h, E g ≤ b h)
    (hW : ∀ g, W ≤ 6 * D g + 12 * γ * E g) :
    W ≤ 48 * (1 + γ / (2 * (k : ℝ))) *
      ((∑ h ∈ range (2*k), b (h+1)) / (2 * (k : ℝ))) := by
  let B := ∑ h ∈ range (2*k), b (h+1)
  have hpartial (h : ℕ) : 0 ≤ ∑ g ∈ range h, E g := sum_nonneg fun _ _ => hE _
  have hDb (h : ℕ) : D h ≤ b h := (le_add_of_nonneg_right (hpartial h)).trans (hp h)
  have hb (h : ℕ) : 0 ≤ b h := (hD h).trans (hDb h)
  have hB : 0 ≤ B := sum_nonneg fun _ _ => hb _
  have splitB : B = (∑ h ∈ range k, b (h+1)) + ∑ h ∈ range k, b (k+h+1) := by
    unfold B
    rw [two_mul]
    exact sum_range_add (fun h => b (h+1)) k k
  have hfirst : (∑ g ∈ range k, D (g+1)) ≤ B := by
    rw [splitB]
    exact (sum_le_sum (fun i _ => hDb (i+1))).trans
      (le_add_of_nonneg_right (sum_nonneg fun _ _ => hb _))
  have hsecond : (k : ℝ) * (∑ g ∈ range k, E (g+1)) ≤ B := by
    have hle (h : ℕ) : (∑ g ∈ range k, E (g+1)) ≤ b (k+h+1) := by
      calc
        _ ≤ ∑ g ∈ range (k+1), E g := by
          rw [sum_range_succ']
          exact le_add_of_nonneg_right (hE 0)
        _ ≤ ∑ g ∈ range (k+h+1), E g :=
          sum_mono_set_of_nonneg hE (range_mono (by omega))
        _ ≤ b (k+h+1) := (le_add_of_nonneg_left (hD _)).trans (hp _)
    rw [splitB]
    have hs := sum_le_sum (s := range k) (fun i _ => hle i)
    simpa using hs.trans (le_add_of_nonneg_left (sum_nonneg
      (s := range k) (f := fun h => b (h+1)) fun _ _ => hb _))
  have htotal := sum_le_sum (s := range k) (fun i _ => hW (i+1))
  simp only [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at htotal
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hscaled : W * (k : ℝ)^2 ≤ 24 * B * k + 12 * γ * B := by
    nlinarith only [mul_le_mul_of_nonneg_left htotal hk'.le,
      mul_le_mul_of_nonneg_left hfirst hk'.le, mul_le_mul_of_nonneg_left hsecond hγ,
      mul_nonneg hB hk'.le]
  calc
    W ≤ (24 * B * k + 12 * γ * B) / (k : ℝ)^2 := (le_div_iff₀ (sq_pos_of_pos hk')).mpr hscaled
    _ = _ := by
      change _ = 48 * (1 + γ / (2 * (k : ℝ))) * (B / (2 * (k : ℝ)))
      field_simp
      ring

end ThreeFlat.Expander

end OAI
