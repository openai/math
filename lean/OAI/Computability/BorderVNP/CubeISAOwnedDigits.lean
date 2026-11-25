import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! # Inserting the fixed row symbol in a product-alphabet address

A row cursor traverses the other coordinates in little-endian order. One division
and one remainder split that address at the chosen grouping coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

/-- Insert a digit at the place with weight `place`, retaining both parts of the old address. -/
def insertDigit (radix place digit tail : ℕ) : ℕ :=
  tail % place + place * (digit + radix * (tail / place))

private theorem consRank {r n : ℕ} (x : Fin r) (f : Fin n → Fin r) :
    (finFunctionFinEquiv (Fin.cons x f) : ℕ) = x.val + r * (finFunctionFinEquiv f : ℕ) := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_succ, finFunctionFinEquiv_apply, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one, pow_succ']
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem insertDigit_step {r : ℕ} (x : Fin r) (place digit tail : ℕ) :
    insertDigit r (r * place) digit (x.val + r * tail) =
      x.val + r * insertDigit r place digit tail := by
  have hx := x.isLt
  have hr : 0 < r := Nat.zero_lt_of_lt hx
  have hm : (x.val + r * tail) % r = x.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
  have hd : (x.val + r * tail) / r = tail := by
    rw [Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hx, Nat.zero_add]
  unfold insertDigit
  rw [Nat.mod_mul, hm, hd, ← Nat.div_div_eq_div_mul, hd]
  ring

/-- The ordinary word-arithmetic formula is the exact `finFunctionFinEquiv` code
of the full tuple with its specified coordinate inserted. -/
theorem rank_insertNth {r n : ℕ} (i : Fin (n+1)) (digit : Fin r) (tail : Fin n → Fin r) :
    (finFunctionFinEquiv (i.insertNth (α := fun _ => Fin r) digit tail) : ℕ) =
      insertDigit r (r^i.val) digit.val (finFunctionFinEquiv tail).val := by
  induction n with
  | zero =>
    obtain rfl : i = 0 := Fin.ext (by have := i.isLt; omega)
    rw [Fin.insertNth_zero', consRank]
    simp [insertDigit, Nat.mod_one]
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      rw [Fin.insertNth_zero', consRank]
      simp [insertDigit, Nat.mod_one]
    | succ i =>
      rw [← Fin.cons_self_tail tail, Fin.insertNth_succ_cons, consRank, ih, consRank,
        Fin.val_succ, pow_succ', insertDigit_step]

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
