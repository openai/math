import OAI.Optimization.LinearProgramming.PriceGame.MomentTrial
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log

/-! Size of the scores, and of the multipliers emitted by recursive trials, in Section 5. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

open Finset

/-- Number of internal layers on a longest branch in this trial. -/
def Trial.height {E : Type*} {r : ℕ} : Trial E r → ℕ
  | .leaf => 0
  | .node _ _ children => univ.sup (fun j => (children j).height) + 1

private theorem mean_le_bound (k : ℕ) (f : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i < k, f i ≤ B) : (∑ i ∈ range k, f i) / k ≤ B := by
  by_cases hk : k = 0
  · simpa [hk] using hB
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))).2
  calc
    (∑ i ∈ range k, f i) ≤ ∑ _i ∈ range k, B :=
      sum_le_sum fun i hi => hf i (mem_range.mp hi)
    _ = B * k := by simp [mul_comm]

theorem roundedScore_le_height_step (C k : ℕ) {σ H : ℝ} (hσ : 0 ≤ σ)
    (hH : H ≤ (C + 2 : ℝ) ^ k) : roundedScore C σ H ≤ (C + 2) ^ (k + 1) := by
  rw [roundedScore, Nat.ceil_le]
  push_cast
  have hB : 0 ≤ (C + 2 : ℝ) ^ k := by positivity
  have hmax : max 0 (H - σ / 2) ≤ (C + 2 : ℝ) ^ k := max_le hB (by linarith)
  calc
    (C : ℝ) * max 0 (H - σ / 2) ≤ C * (C + 2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
    _ ≤ (C + 2 : ℝ) ^ (k + 1) := by rw [pow_succ]; nlinarith

/-- The actual rational score computed by a trial has polynomially bounded value
when the branching depth is logarithmic. -/
theorem Trial.score_le_height {E : Type*} [Fintype E] {r : ℕ}
    (C : ℕ) (σ : ℚ) (η : ℝ) (hσ : 0 ≤ σ) (tr : Trial E r)
    (w : E → ℝ) (ha : tr.Admissible C σ η w) (e : E) :
    tr.score C σ e ≤ (C + 2) ^ tr.height := by
  have hσ' : (0 : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hσ
  induction tr generalizing w with
  | leaf => simp [Trial.score, Trial.height]
  | node mask gain children ih =>
    obtain ⟨hg, _, hc⟩ := ha
    let k := univ.sup fun j => (children j).height
    change (Trial.node mask gain children).score C σ e ≤ (C + 2) ^ (k + 1)
    have hbase : (1 : ℝ) ≤ (C + 2 : ℝ) ^ k := one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) C])
    rw [Trial.score_node]
    simp only [Rat.cast_natCast]
    split
    · apply roundedScore_le_height_step C k hσ'
      exact mean_le_bound _ _ (zero_le_one.trans hbase) fun i hi =>
        ((le_abs_self _).trans (hg i hi e)).trans hbase
    · apply roundedScore_le_height_step C k hσ'
      apply mean_le_bound _ _ (zero_le_one.trans hbase)
      intro i hi
      let j : Fin (2 * r) := ⟨i, hi⟩
      have hchild : childScoreAt C σ children i e = (children j).score C σ e := by
        simp [childScoreAt, probeAt, hi, j]
      rw [hchild]
      have hh : (children j).height ≤ k :=
        Finset.le_sup (f := fun p => (children p).height) (mem_univ j)
      exact_mod_cast (ih j _ (hc j)).trans
        (pow_le_pow_right' (by omega : 1 ≤ C + 2) hh)

/-- If the trial follows the depth (D = ⌊log₂ N⌋+1), the bit length of the exact
integer multiplier is at most a fixed polynomial in the number of root coordinates. -/
theorem Trial.multiplier_size_le {E : Type*} [Fintype E] {r : ℕ}
    (C B N : ℕ) (σ : ℚ) (η : ℝ) (hσ : 0 ≤ σ) (hN : N ≠ 0) (hC : C + 2 ≤ 2 ^ B)
    (tr : Trial E r) (hd : tr.height ≤ Nat.log 2 N + 1)
    (w : E → ℝ) (ha : tr.Admissible C σ η w) (e : E) :
    Nat.size (2 ^ tr.score C σ e) ≤ (2 * N) ^ B + 1 := by
  rw [Nat.size_pow]
  apply Nat.add_le_add_right
  calc
    tr.score C σ e ≤ (C + 2) ^ tr.height := tr.score_le_height C σ η hσ w ha e
    _ ≤ (C + 2) ^ (Nat.log 2 N + 1) := pow_le_pow_right' (by omega) hd
    _ ≤ (2 ^ B) ^ (Nat.log 2 N + 1) := Nat.pow_le_pow_left hC _
    _ = (2 * 2 ^ Nat.log 2 N) ^ B := by
      rw [← pow_mul, Nat.mul_comm B _, pow_mul, pow_succ, Nat.mul_comm (2 ^ Nat.log 2 N) 2]
    _ ≤ (2 * N) ^ B := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hN)) B

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
