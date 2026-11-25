import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Locality and rounding bounds for a shortening epoch

A moved tile has only boundedly many possible destination neighbors, and each
destination has only boundedly many source neighbors. The first estimate
below bounds the change in the spatial concentration of the wire counts
under such a move. The second controls rounding back to tile sites, when a
positive-length segment crosses a tile boundary with probability at most
a fixed constant times its length. Neither estimate requires independence
between the segments of a pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Squared concentration of local counts after a move with bounded numbers
of source neighbors and destination neighbors. -/
theorem sum_sq_locality [DecidableEq α] (sources : β → Finset α) (old : α → ℝ) (new : β → ℝ)
    (fanIn fanOut : ℕ) (hnew : ∀ b, 0 ≤ new b)
    (hload : ∀ b, new b ≤ ∑ a ∈ sources b, old a)
    (hIn : ∀ b, (sources b).card ≤ fanIn)
    (hOut : ∀ a, (univ.filter fun b => a ∈ sources b).card ≤ fanOut) :
    ∑ b, new b ^ 2 ≤ (fanIn : ℝ) * fanOut * ∑ a, old a ^ 2 := by
  classical
  have hlocal (b : β) :
      new b ^ 2 ≤ (fanIn : ℝ) * ∑ a ∈ sources b, old a ^ 2 := by
    calc
      _ ≤ (∑ a ∈ sources b, old a) ^ 2 := by
        apply pow_le_pow_left₀ (hnew b) (hload b)
      _ ≤ ((sources b).card : ℝ) * ∑ a ∈ sources b, old a ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hIn b)
        (sum_nonneg fun a _ => sq_nonneg (old a))
  have hsum :
      (∑ b, ∑ a ∈ sources b, old a ^ 2) ≤ (fanOut : ℝ) * ∑ a, old a ^ 2 := by
    calc
      _ = ∑ b, ∑ a, if a ∈ sources b then old a ^ 2 else 0 := by
        simp_rw [← sum_filter]
        simp
      _ = ∑ a, ∑ b, if a ∈ sources b then old a ^ 2 else 0 := sum_comm
      _ ≤ ∑ a, (fanOut : ℝ) * old a ^ 2 := by
        apply sum_le_sum
        intro a _
        rw [← sum_filter]
        simpa using mul_le_mul_of_nonneg_right
          (show ((univ.filter fun b => a ∈ sources b).card : ℝ) ≤ fanOut
            by exact_mod_cast hOut a) (sq_nonneg (old a))
      _ = _ := (mul_sum _ _ _).symm
  calc
    _ ≤ ∑ b, (fanIn : ℝ) * ∑ a ∈ sources b, old a ^ 2 :=
      sum_le_sum fun b _ => hlocal b
    _ = (fanIn : ℝ) * ∑ b, ∑ a ∈ sources b, old a ^ 2 := (mul_sum _ _ _).symm
    _ ≤ _ := by rw [mul_assoc]; gcongr

/-- Some global motion leaves at most the expected upper bound on the total
nonlocal bits. The widths count multiplicities of the original segments. -/
theorem exists_site_rounding (prob : α → ℝ) (width length : β → ℝ)
    (separate : α → β → Bool) (C : ℝ) (hp : ∀ u, 0 ≤ prob u)
    (ht : ∑ u, prob u = 1) (hw : ∀ b, 0 ≤ width b)
    (hcross : ∀ b, (∑ u, if separate u b then prob u else 0) ≤ C * length b) :
    ∃ u, (∑ b, if separate u b then width b else 0) ≤ C * ∑ b, width b * length b := by
  classical
  let crossing (u : α) := ∑ b, if separate u b then width b else 0
  have hexp : ∑ u, prob u * crossing u ≤ C * ∑ b, width b * length b := by
    calc
      _ = ∑ b, width b * ∑ u, if separate u b then prob u else 0 := by
        unfold crossing
        simp_rw [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro b _
        apply sum_congr rfl
        intro u _
        cases separate u b <;> simp [mul_comm]
      _ ≤ ∑ b, width b * (C * length b) := by
        exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hcross b) (hw b)
      _ = _ := by simp_rw [mul_left_comm (width _) C, mul_sum]
  by_contra! h
  obtain ⟨u, hu⟩ : ∃ u, 0 < prob u := by
    by_contra! hzero
    have : ∑ u, prob u ≤ 0 := sum_nonpos fun i _ => hzero i
    linarith
  have hstrict : ∑ u, prob u * (C * ∑ b, width b * length b) < ∑ u, prob u * crossing u :=
    sum_lt_sum (fun v _ => mul_le_mul_of_nonneg_left (h v).le (hp v))
      ⟨u, mem_univ u, mul_lt_mul_of_pos_left (h u) hu⟩
  rw [← sum_mul, ht, one_mul] at hstrict
  linarith

end Epoch

end BorderVNP
end Computability
end OAI
