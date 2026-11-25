import OAI.ThreeFlat.ExpanderBasic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Rounding sparse symmetric transition matrices to regular multigraphs -/

noncomputable section
namespace ThreeFlat.Expander

open Finset Matrix
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private def ceilCount (G : Matrix V V ℝ) (h : ℕ) (i j : V) : ℕ :=
  ⌈((h : ℝ) / 2) * G i j⌉₊

/-- Round half of the scaled transition probabilities up to integers, then
fill the remaining degree at each vertex with loops. -/
def roundedCounts (G : Matrix V V ℝ) (h : ℕ) (i j : V) : ℕ :=
  ceilCount G h i j + if i = j then h - ∑ k, ceilCount G h i k else 0

theorem roundedCounts_symmetric {G : Matrix V V ℝ} (hsym : ∀ i j, G i j = G j i)
    (h : ℕ) (i j : V) : roundedCounts G h i j = roundedCounts G h j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp [roundedCounts, ceilCount, hij, Ne.symm hij, hsym i j]

private theorem sum_ceilCount_le {G : Matrix V V ℝ} (hG : G ∈ rowStochastic ℝ V)
    {s h : ℕ} (hsupp : ∀ i, (univ.filter fun j => G i j ≠ 0).card ≤ s)
    (hs : 2*s ≤ h) (i : V) : ∑ j, ceilCount G h i j ≤ h := by
  have point (j : V) : (ceilCount G h i j : ℝ) ≤
      ((h : ℝ)/2) * G i j + (if G i j ≠ 0 then 1 else 0) := by
    by_cases hz : G i j = 0
    · simp [ceilCount, hz]
    · rw [ite_eq_left hz]
      have hnonneg : 0 ≤ ((h : ℝ)/2) * G i j :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg h) (by norm_num)) (hG.1 i j)
      exact (Nat.ceil_lt_add_one hnonneg).le
  have hrow := sum_le_sum (s := univ) fun j _ => point j
  rw [sum_add_distrib, ← mul_sum, sum_row_of_mem_rowStochastic hG, mul_one,
    sum_boole] at hrow
  have hsize : ((univ.filter fun j => G i j ≠ 0).card : ℝ) ≤ s := by exact_mod_cast hsupp i
  have hroom : 2*(s : ℝ) ≤ h := by exact_mod_cast hs
  have : ∑ j, (ceilCount G h i j : ℝ) ≤ h := by linarith
  exact_mod_cast this

/-- The rounded multigraph is regular when its prescribed degree is at least
twice the row support of the transition matrix. -/
theorem sum_roundedCounts {G : Matrix V V ℝ} (hG : G ∈ rowStochastic ℝ V)
    {s h : ℕ} (hsupp : ∀ i, (univ.filter fun j => G i j ≠ 0).card ≤ s)
    (hs : 2*s ≤ h) (i : V) : ∑ j, roundedCounts G h i j = h := by
  simp only [roundedCounts, sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
  exact Nat.add_sub_of_le (sum_ceilCount_le hG hsupp hs i)

/-- Each rounded transition retains at least half the original probability. -/
theorem le_two_mul_transition_roundedCounts (G : Matrix V V ℝ) {h : ℕ} (hh : 0 < h)
    (i j : V) : G i j ≤ 2 * transition (roundedCounts G h) h i j := by
  have hceil : ((h : ℝ)/2) * G i j ≤ (ceilCount G h i j : ℝ) := Nat.le_ceil _
  have hpad : ceilCount G h i j ≤ roundedCounts G h i j := Nat.le_add_right _ _
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  change G i j ≤ 2 * ((roundedCounts G h i j : ℝ) / h)
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  have hc : (ceilCount G h i j : ℝ) ≤ roundedCounts G h i j := by exact_mod_cast hpad
  linarith

/-- Rounding increases the quadratic Poincaré constant by a factor of two. -/
theorem Bound.roundedCounts {X : Type*} [PseudoMetricSpace X] {G : Matrix V V ℝ}
    {γ : ℝ} (hb : Bound G X γ) (hγ : 0 ≤ γ) {h : ℕ} (hh : 0 < h) :
    Bound (transition (Expander.roundedCounts G h) h) X (2 * γ) := by
  intro x
  let T := transition (Expander.roundedCounts G h) h
  have bound (i j : V) := mul_le_mul_of_nonneg_right
    (le_two_mul_transition_roundedCounts G hh i j) (sq_nonneg (dist (x i) (x j)))
  have hrow (i : V) : (∑ j, G i j * dist (x i) (x j)^2) ≤
      2 * ∑ j, T i j * dist (x i) (x j)^2 := by
    simpa only [T, mul_assoc, ← mul_sum] using sum_le_sum (s := univ) (fun j _ => bound i j)
  have he : energy G x ≤ 2 * energy T x := by
    simpa only [energy, avg_mul] using avg_le hrow
  calc
    variance x ≤ γ * energy G x := hb x
    _ ≤ γ * (2 * energy T x) := mul_le_mul_of_nonneg_left he hγ
    _ = _ := by ring

end ThreeFlat.Expander

end
end OAI
