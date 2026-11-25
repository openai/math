import OAI.Hierarchy.FactorBuckets
import Mathlib.Algebra.Order.Floor.Div

namespace OAI
/-! # The public integer thresholds for the geometric factor classes -/

namespace Hierarchy.FactorBucket

open scoped Nat

/-- Entry i of the common public table. It depends only on its address. -/
def threshold (i : ℕ) : ℕ := (21^i:ℕ) ⌈/⌉ (20^i)

theorem threshold_le (i x : ℕ) : threshold i ≤ x ↔ 21^i ≤ 20^i*x :=
  ceilDiv_le_iff_le_mul (by positivity : 0 < (20:ℕ)^i)

theorem threshold_pos (i : ℕ) : 0 < threshold i := by
  by_contra! h
  have bad := (threshold_le i 0).mp h
  simp at bad

/-- A scan returns the last threshold the integer resource meets, with
label zero for an empty resource. -/
def scanned (x : ℕ) : ℕ → ℕ
  | 0 => if threshold 0 ≤ x then 1 else 0
  | n+1 => if threshold (n+1) ≤ x then (n+1)+1 else scanned x n

private theorem scan_greatest (x n : ℕ) (pos : x ≠ 0) :
    scanned x n = Nat.findGreatest (fun j => 21^j ≤ 20^j*x) n + 1 := by
  induction n with
  | zero => simp [scanned,threshold_le, Nat.one_le_iff_ne_zero.mpr pos]
  | succ n ih => by_cases h : 21^(n+1) ≤ 20^(n+1)*x <;> simp [scanned,threshold_le,ih,h]

theorem scanned_eq_label (w x : ℕ) : scanned x (20*(w+1)) = (label w x).val := by
  by_cases zero : x=0
  · subst x
    have empty (n : ℕ) : scanned 0 n=0 := by
      induction n with
      | zero => simp [scanned, not_le.mpr (threshold_pos 0)]
      | succ n ih => simp [scanned, not_le.mpr (threshold_pos _),ih]
    simp [empty,label]
  · simpa [label_val_of_ne zero] using scan_greatest x (20*(w+1)) zero

/-- A threshold occupies one native 64w-bit word for w positive, even
though the numerator and denominator defining it may be larger. -/
theorem threshold_word {w i : ℕ} (positive : 0<w) (bounded : i≤20*(w+1)) :
    threshold i < 2^(64*w) := by
  have ratio : (21/20:ℝ)^i ≤ (4:ℝ)^(w+1) := calc
    _ ≤ (21/20:ℝ)^(20*(w+1)) := pow_le_pow_right₀ (by norm_num) bounded
    _ = ((21/20:ℝ)^20)^(w+1) := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have clear := (div_le_iff₀ (by positivity : 0<(20:ℝ)^i)).mp (by simpa [div_pow] using ratio)
  have bound : threshold i ≤ 4^(w+1) := (threshold_le _ _).mpr (by exact_mod_cast (by
    simpa [mul_comm] using clear : (21:ℝ)^i ≤ 20^i*4^(w+1)))
  apply bound.trans_lt
  rw [show (4:ℕ)=2^2 by decide, ←pow_mul]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

end Hierarchy.FactorBucket

end OAI
