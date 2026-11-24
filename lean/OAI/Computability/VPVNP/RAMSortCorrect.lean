import OAI.Computability.VPVNP.RAMSortNetwork
import OAI.Computability.VPVNP.RAMSortPulse
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Correctness of the bitonic record sort

At any threshold a bitonic block has one cyclic interval of ones. Opposite
comparisons produce a smaller and a larger pulse. Recursing sorts these into
the two halves of the correct output, whose one counts are determined by
truncating the old one count at half the block size. Thresholding then lifts
the Boolean result to any linearly ordered record type.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

private theorem width_succ (b : ℕ) : 2 ^ (b + 1) = 2 * 2 ^ b := by
  rw [Nat.pow_succ, Nat.mul_comm]

private def pulseBlock (b s k : ℕ) : Wires b Bool := fun i ↦ pulse (2 ^ b) s k i

/-- The Boolean block with `k` ones in the specified order. -/
def orderedBits (b : ℕ) (up : Bool) (k : ℕ) : Wires b Bool :=
  fun i ↦ if up then decide (2 ^ b - k ≤ i.val) else decide (i.val < k)

private theorem min_bool (x y : Bool) : min x y = (x && y) := by cases x <;> cases y <;> rfl
private theorem max_bool (x y : Bool) : max x y = (x || y) := by cases x <;> cases y <;> rfl

private theorem splitMin (b s k : ℕ) :
    (fun i ↦ min (lo (pulseBlock (b+1) s k) i) (hi (pulseBlock (b+1) s k) i)) =
      pulseBlock b s (k - 2 ^ b) := by
  funext i
  change min (pulse (2 ^ (b+1)) s k i.val) (pulse (2 ^ (b+1)) s k (i.val + 2^b)) = _
  rw [min_bool, width_succ, pulse_and (Nat.pow_pos (by decide))]
  rfl

private theorem splitMax (b s k : ℕ) :
    (fun i ↦ max (lo (pulseBlock (b+1) s k) i) (hi (pulseBlock (b+1) s k) i)) =
      pulseBlock b s (min k (2 ^ b)) := by
  funext i
  change max (pulse (2 ^ (b+1)) s k i.val) (pulse (2 ^ (b+1)) s k (i.val + 2^b)) = _
  rw [max_bool, width_succ, pulse_or (Nat.pow_pos (by decide))]
  rfl

private theorem merge_pulse (b : ℕ) (up : Bool) (s k : ℕ) (hk : k ≤ 2 ^ b) :
    merge b up (pulseBlock b s k) = orderedBits b up k := by
  induction b generalizing k up with
  | zero =>
    funext i
    have hi : i.val = 0 := by have := i.isLt; simp at this; omega
    cases up <;> simp [merge, orderedBits, pulseBlock, pulse] <;> omega
  | succ b ih =>
    have hwidth := width_succ b
    have hsmall : k - 2 ^ b ≤ 2 ^ b := by omega
    have hlarge : min k (2 ^ b) ≤ 2 ^ b := min_le_right ..
    cases up <;> simp only [merge, lower, upper, Bool.false_eq_true, ite_false, ite_true,
      splitMin, splitMax, ih _ _ hsmall, ih _ _ hlarge]
    all_goals
      apply eq_of_halves <;> simp only [lo_join, hi_join]
      all_goals
        funext i
        have := i.isLt
        simp only [orderedBits, lo, hi, Bool.false_eq_true, ite_false, ite_true, decide_eq_decide]
        omega

private theorem bits_join_pulse (b k t : ℕ) (hk : k ≤ 2 ^ b) (ht : t ≤ 2 ^ b) :
    join (orderedBits b true k) (orderedBits b false t) =
      pulseBlock (b+1) (2 * 2 ^ b - (2 ^ b - k)) (k + t) := by
  funext i
  have hi := i.isLt
  have hw := width_succ b
  have hseg := pulse_of_segments (n := 2 ^ b) (a := 2 ^ b - k) (b := t)
    (Nat.sub_le ..) ht (i := i.val) (by omega)
  have hc : 2 ^ b - (2 ^ b - k) = k := by omega
  rw [hc] at hseg
  simp only [pulseBlock, hw, hseg, join, orderedBits, ite_true, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- The network sorts every Boolean block into a single run of zeros and a
single run of ones in the requested order. -/
theorem sort_bits (b : ℕ) (up : Bool) (x : Wires b Bool) :
    ∃ k ≤ 2 ^ b, sort b up x = orderedBits b up k := by
  induction b generalizing up with
  | zero =>
    refine ⟨if x 0 then 1 else 0, ?_, ?_⟩
    · split <;> decide
    · funext i
      have hi : i = 0 := Fin.ext (by have := i.isLt; simp at this; omega)
      rw [hi]
      cases h : x 0 <;> cases up <;> simp [sort, orderedBits, h]
  | succ b ih =>
    obtain ⟨k, hk, h₀⟩ := ih true (lo x)
    obtain ⟨t, ht, h₁⟩ := ih false (hi x)
    have hkt : k + t ≤ 2 ^ (b + 1) := by have := width_succ b; omega
    refine ⟨k + t, hkt, ?_⟩
    rw [sort, h₀, h₁, bits_join_pulse b k t hk ht, merge_pulse _ _ _ _ hkt]

private theorem cut_mono {α : Type*} [LinearOrder α] (a : α) :
    Monotone (fun x ↦ decide (a ≤ x)) := by
  intro x y h
  exact Bool.le_iff_imp.mpr (by simpa using fun hax : a ≤ x ↦ hax.trans h)

/-- Batcher's ascending network sorts the entire block. -/
theorem sort_monotone {α : Type*} [LinearOrder α] (b : ℕ) (x : Wires b α) :
    Monotone (sort b true x) := by
  intro i j hij
  let cut := fun a : α ↦ decide (sort b true x i ≤ a)
  have hmap := sort_map cut (cut_mono _) b true x
  obtain ⟨k, _, hbits⟩ := sort_bits b true (cut ∘ x)
  rw [hbits] at hmap
  have hi := congrFun hmap i
  have hj := congrFun hmap j
  simp [cut, orderedBits] at hi hj
  exact hj.mpr (hi.trans (Nat.add_le_add_right hij k))

/-- Odd-numbered intermediate blocks are sorted in descending order. -/
theorem sort_antitone {α : Type*} [LinearOrder α] (b : ℕ) (x : Wires b α) :
    Antitone (sort b false x) := by
  intro i j hij
  let cut := fun a : α ↦ decide (sort b false x j ≤ a)
  have hmap := sort_map cut (cut_mono _) b false x
  obtain ⟨k, _, hbits⟩ := sort_bits b false (cut ∘ x)
  rw [hbits] at hmap
  have hi := congrFun hmap i
  have hj := congrFun hmap j
  simp [cut, orderedBits] at hi hj
  exact hi.mpr (lt_of_le_of_lt hij hj)

end RAMSort

end VPVNP
end Computability
end OAI
