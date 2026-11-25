import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Partition into recursive Walsh pieces

The digit at position `j` counts the pieces of length `2 * A ^ j`.
One trailing bit uses the direct butterfly when the number of selected bits is odd.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open Finset

/-- The multiplicities of the even Walsh pieces in increasing order of length. -/
def walshPieceDigits (A s : ℕ) : List ℕ := A.digits (s / 2)

theorem walsh_piece_partition (A s : ℕ) :
    (∑ j : Fin (walshPieceDigits A s).length,
      (walshPieceDigits A s).get j * (2 * A ^ (j : ℕ))) + s % 2 = s := by
  have h := Nat.ofDigits_digits A (s / 2)
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn] at h
  have h' : (∑ j : Fin (walshPieceDigits A s).length,
      (walshPieceDigits A s).get j * A ^ (j : ℕ)) = s / 2 := h
  simp_rw [mul_left_comm _ 2 _]
  rw [← Finset.mul_sum, h']
  omega

theorem walsh_piece_cost_bound {A : ℕ} (hA : 1 < A) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℕ, (∑ j : Fin (walshPieceDigits A s).length,
      ((walshPieceDigits A s).get j : ℝ) * ((2 : ℝ) * (A : ℝ) ^ (j : ℕ)) ^ ρ)
      ≤ C * (s : ℝ) ^ ρ := by
  let r := (A : ℝ) ^ ρ
  have hr : 1 < r := Real.one_lt_rpow (by exact_mod_cast hA) hρ
  have hr' : 0 < r - 1 := sub_pos.mpr hr
  refine ⟨(A * (2 : ℝ) ^ ρ) * r / (r - 1), by positivity, fun s => ?_⟩
  let digits := walshPieceDigits A s
  change (∑ j : Fin digits.length, (digits.get j : ℝ) * ((2 : ℝ) * A ^ (j : ℕ)) ^ ρ) ≤ _
  by_cases hs : s / 2 = 0
  · have hd : digits.length = 0 := by simp [digits, walshPieceDigits, hs]
    have : IsEmpty (Fin digits.length) := hd ▸ Fin.isEmpty'
    rw [Finset.sum_of_isEmpty]
    positivity
  have hlen : (A : ℝ) ^ digits.length ≤ A * (s : ℝ) := by
    exact_mod_cast (Nat.base_pow_length_digits_le A (s / 2) hA hs).trans
      (Nat.mul_le_mul_left A (Nat.div_le_self ..))
  have hgeom : (∑ j : Fin digits.length, r ^ (j : ℕ)) ≤ r * (s : ℝ) ^ ρ / (r - 1) := by
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hr.ne']
    apply div_le_div_of_nonneg_right _ hr'.le
    have hpow := Real.rpow_le_rpow (by positivity) hlen hρ.le
    rw [← Real.rpow_pow_comm (Nat.cast_nonneg A), Real.mul_rpow (by positivity)
      (Nat.cast_nonneg s)] at hpow
    exact (sub_le_self _ zero_le_one).trans hpow
  calc
    _ ≤ ∑ j : Fin digits.length, (A * (2 : ℝ) ^ ρ) * r ^ (j : ℕ) := by
      apply sum_le_sum
      intro j _
      have hd : (digits.get j : ℝ) ≤ A := by
        exact_mod_cast (Nat.digits_lt_base hA (List.get_mem digits j)).le
      rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_pow_comm (Nat.cast_nonneg A)]
      dsimp only [r]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hd (by positivity)
    _ = (A * (2 : ℝ) ^ ρ) * ∑ j : Fin digits.length, r ^ (j : ℕ) := (mul_sum ..).symm
    _ ≤ (A * (2 : ℝ) ^ ρ) * (r * (s : ℝ) ^ ρ / (r - 1)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by ring

/-- A per-piece recursion tree with branching `σ` and depth `j` has at
most `(σ + 1) ^ j` nodes. Summing this bound over all pieces gives a
polynomial bound on the number of invocations requiring local setup. -/
theorem walsh_piece_setup_bound {A : ℕ} (hA : 1 < A) (σ s : ℕ) :
    (∑ j : Fin (walshPieceDigits A s).length,
      ((walshPieceDigits A s).get j : ℝ) * ((σ : ℝ) + 1) ^ (j : ℕ)) ≤ (s : ℝ) ^ (σ + 1) := by
  let digits := walshPieceDigits A s
  have hd : digits.sum ≤ s := calc
    _ ≤ Nat.ofDigits A digits := Nat.sum_le_ofDigits _ hA.le
    _ = s / 2 := Nat.ofDigits_digits ..
    _ ≤ s := Nat.div_le_self ..
  have hsum : (∑ j : Fin digits.length, digits.get j) ≤ s := by
    simpa only [← List.sum_ofFn, List.ofFn_get] using hd
  have hσ : σ + 1 ≤ A ^ σ :=
    σ.lt_two_pow_self.trans_le (Nat.pow_le_pow_left hA σ)
  have hnum : (∑ j : Fin digits.length, digits.get j * (σ + 1) ^ (j : ℕ)) ≤ s ^ (σ+1) := calc
    _ ≤ ∑ j : Fin digits.length, digits.get j * s ^ σ := by
      apply sum_le_sum
      intro j _
      have hwidth : A ^ (j : ℕ) ≤ s / 2 :=
        (Nat.lt_digits_length_iff hA _).mp j.isLt
      apply Nat.mul_le_mul_left
      calc
        _ ≤ (A ^ σ) ^ (j : ℕ) := Nat.pow_le_pow_left hσ _
        _ = (A ^ (j : ℕ)) ^ σ := Nat.pow_right_comm ..
        _ ≤ s ^ σ := Nat.pow_le_pow_left (hwidth.trans (Nat.div_le_self ..)) _
    _ = (∑ j : Fin digits.length, digits.get j) * s ^ σ := (sum_mul ..).symm
    _ ≤ s * s ^ σ := Nat.mul_le_mul_right _ hsum
    _ = _ := by rw [pow_succ']
  exact_mod_cast hnum

end NearSquareRoot
end Computability
end OAI
