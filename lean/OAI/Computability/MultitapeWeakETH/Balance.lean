import OAI.Computability.MultitapeWeakETH.Terminals
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Expect

/-! # Averaging the paired-terminal demand over all shifts -/

namespace OAI.Computability.MultitapeWeakETH

open Finset
open scoped BigOperators

/-- Transfer the paired entropy inequality to the common supply. The lengths
depend on the shift, and the distance error is charged against the independent
uniform terminal-pair law only after averaging. -/
theorem supply_from_entropy {N b n : ℕ} [NeZero N] [NeZero b] (periods offset : Fin N → ℕ)
    (positive : ∀ t, 0 < periods t) (length : ∀ t, periods t*(N*b) ≤ n)
    (d : Fin N → Fin N → ℝ) (rates : (t : Fin N) → Fin (periods t*(N*b)) → ℝ)
    (range : ∀ t j, 0 ≤ rates t j ∧ rates t j ≤ 1)
    (logDensity advice : Fin N → ℝ) (S margin : ℝ)
    (source : ∀ t, (periods t*(N*b):ℕ)+logDensity t ≤ ∑ j, rates t j)
    (retention : ∀ t, margin ≤ (periods t*(N*b):ℕ)+logDensity t-advice t)
    (paired : ∀ t, (∑ j, rates t j * d (foldedTerminal (offset t) j)
      (foldedTerminal (offset t) j+t)) ≤ S+advice t) :
    margin - (n:ℝ)*(𝔼 i, 𝔼 j, |d i j-1|) ≤ S := by
  let len (t) := periods t*(N*b)
  let cost (t : Fin N) (j : Fin (len t)) :=
    d (foldedTerminal (offset t) j) (foldedTerminal (offset t) j+t)
  have perShift (t : Fin N) : margin-S ≤ (n:ℝ)*(𝔼 j : Fin (len t), |cost t j-1|) := by
    have demand : (∑ j, rates t j) - (∑ j, rates t j * cost t j) ≤ ∑ j, |cost t j-1| := by
      rw [← sum_sub_distrib]
      apply sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (neg_le_abs (cost t j-1)) (range t j).1
      have hh := mul_le_mul_of_nonneg_right (range t j).2 (abs_nonneg (cost t j-1))
      linarith only [h,hh]
    have lpos : 0 < len t := Nat.mul_pos (positive t) (Nat.mul_pos (NeZero.pos N) (NeZero.pos b))
    have scale : (∑ j, |cost t j-1|) = (len t:ℝ)*(𝔼 j, |cost t j-1|) := by
      rw [Fintype.expect_eq_sum_div_card,Fintype.card_fin,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr lpos.ne')]
    have hlen := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ) |>.mpr (length t))
      (expect_nonneg (s := univ) (fun j _ => abs_nonneg (cost t j-1)))
    have price : (∑ j, rates t j*cost t j) ≤ S+advice t := paired t
    rw [scale] at demand
    linarith only [demand,price,source t,retention t,hlen]
  have avg := expect_le_expect (s := univ) (fun t _ => perShift t)
  rw [Fintype.expect_const,← mul_expect] at avg
  have law := terminal_pair_law (b := b) periods offset positive (fun i j => |d i j-1|)
  change (𝔼 t, 𝔼 j, |cost t j-1|) = _ at law
  rw [law] at avg
  linarith

end OAI.Computability.MultitapeWeakETH
