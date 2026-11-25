import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.ByContra

namespace OAI
/-! # Balanced integer slices of a tagged payload -/

namespace Hierarchy.TaggedWidthSlices

open scoped BigOperators

/-- The minimum number of slots of capacity `C` needed for `w` bits. -/
def count (w C : ℕ) : ℕ := w ⌈/⌉ C

/-- The first remainder-many slices receive one additional bit. -/
def width (w C : ℕ) (i : Fin (count w C)) : ℕ :=
  w / count w C + if i.val < w % count w C then 1 else 0

variable {w C B : ℕ}

theorem count_le_iff (hC : 0 < C) : count w C ≤ B ↔ w ≤ B*C := by
  simpa only [count, Nat.mul_comm B C] using
    (ceilDiv_le_iff_le_mul hC : w ⌈/⌉ C ≤ B ↔ w ≤ C*B)

theorem count_le (hC : 0 < C) (bound : w ≤ B*C) : count w C ≤ B :=
  (count_le_iff hC).mpr bound

theorem capacity (hC : 0 < C) : w ≤ count w C*C :=
  (count_le_iff hC).mp le_rfl

theorem count_pos (hw : 0 < w) (hC : 0 < C) : 0 < count w C := by
  by_contra! none
  have impossible := (count_le_iff hC).mp none
  omega

private theorem extras (k r : ℕ) (hr : r ≤ k) :
    (∑ i : Fin k, if i.val < r then 1 else 0) = r := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r then 1 else 0) k, Finset.sum_boole]
  have filter : (Finset.range k).filter (· < r) = Finset.range r := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [filter]

theorem sum_width (hC : 0 < C) : (∑ i : Fin (count w C), width w C i) = w := by
  by_cases zero : w = 0
  · subst w
    simp [width, count]
  · have hk := count_pos (Nat.pos_of_ne_zero zero) hC
    simp only [width, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, extras _ _ (Nat.mod_lt w hk).le]
    exact Nat.div_add_mod w (count w C)

theorem width_le (hC : 0 < C) (i : Fin (count w C)) : width w C i ≤ C := by
  have hk : 0 < count w C := Nat.zero_lt_of_lt i.isLt
  have room := capacity (w:=w) hC
  have total := Nat.div_add_mod w (count w C)
  have q : w / count w C ≤ C := Nat.le_of_mul_le_mul_left (by omega) hk
  unfold width
  split
  · rename_i tall
    have strict : w / count w C < C := by
      by_contra! small
      have := Nat.mul_le_mul_left (count w C) small
      omega
    omega
  · omega

theorem width_pos (hw : 0 < w) (hC : 0 < C) (i : Fin (count w C)) : 0 < width w C i := by
  have few : count w C ≤ w := count_le hC (Nat.le_mul_of_pos_right w hC)
  have quotient := Nat.div_pos few (count_pos hw hC)
  unfold width
  omega

/-- Widths differ by at most one bit for every pair of slots. -/
theorem balanced (i j : Fin (count w C)) : width w C i ≤ width w C j + 1 := by
  unfold width
  split <;> split <;> omega

/-- A split payload above capacity spends at least half a slot, up to one bit,
on each slice. This estimate is uniform over the slice index. -/
theorem cap_le_twice_succ_width (hC : 0 < C) (wide : C ≤ w) (i : Fin (count w C)) :
    C ≤ 2*(width w C i + 1) := by
  let k := count w C
  have hk : 0 < k := count_pos (hC.trans_le wide) hC
  have padded : k*C ≤ w+C-1 := Nat.div_mul_le_self _ _
  have total := Nat.div_add_mod w k
  have leftover := Nat.mod_lt w hk
  have rounded : w < k*(w/k+1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have strict : k*C < k*(2*(w/k+1)) := calc
    k*C ≤ 2*w := by omega
    _ < 2*(k*(w/k+1)) := Nat.mul_lt_mul_of_pos_left rounded (by decide)
    _ = k*(2*(w/k+1)) := by ac_rfl
  have lower := Nat.lt_of_mul_lt_mul_left strict
  change C ≤ 2*(w/k+(if i.val < w%k then 1 else 0)+1)
  split <;> omega

end Hierarchy.TaggedWidthSlices

end OAI
