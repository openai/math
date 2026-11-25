import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-! Clearing denominators of the expert weights in the balanced-price market. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Denominator

open scoped BigOperators

variable {E : Type*} [Fintype E]

/-- A common denominator that is computable directly from the input rational weights. -/
def denominator (weight : E → ℚ) : ℕ := ∏ e, (weight e).den

theorem denominator_pos (weight : E → ℚ) : 0 < denominator weight :=
  Finset.prod_pos fun e _ => (weight e).den_pos

theorem den_dvd_denominator (weight : E → ℚ) (e : E) : (weight e).den ∣ denominator weight :=
  Finset.dvd_prod_of_mem (fun i => (weight i).den) (Finset.mem_univ e)

/-- When the positive rational weight has denominator dividing `Q`, this is its integral
supply in units of `1 / Q`. -/
def qty (Q : ℕ) (weight : ℚ) : ℕ := weight.num.natAbs * (Q / weight.den)

theorem cast_qty {Q : ℕ} {weight : ℚ} (hw : 0 ≤ weight) (hd : weight.den ∣ Q) :
    (qty Q weight : ℚ) = Q * weight := by
  have hnum : (weight.num.natAbs : ℚ) = (weight.num : ℚ) := by
    calc
      (weight.num.natAbs : ℚ) = ((weight.num.natAbs : ℤ) : ℚ) := (Int.cast_natCast _).symm
      _ = (weight.num : ℚ) := congrArg (fun z : ℤ => (z : ℚ))
        (Int.eq_natAbs_of_nonneg (Rat.num_nonneg.mpr hw)).symm
  have hn : (weight.num : ℚ) = weight * (weight.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast weight.den_ne_zero)).mp weight.num_div_den
  have hfactor : ((Q / weight.den : ℕ) : ℚ) * weight.den = Q := by
    exact_mod_cast Nat.div_mul_cancel hd
  rw [qty, Nat.cast_mul, hnum, hn, ← hfactor]
  ring

theorem qty_pos {Q : ℕ} {weight : ℚ} (hw : 0 < weight) (hQ : 0 < Q)
    (hd : weight.den ∣ Q) : 0 < qty Q weight := by
  have h : (0 : ℚ) < (Q : ℚ) * weight := mul_pos (by exact_mod_cast hQ) hw
  rw [← cast_qty hw.le hd] at h
  exact_mod_cast h

theorem size_mul_le_add (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_right b (Nat.lt_size_self a).le).trans_lt
    (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b) (Nat.two_pow_pos _))

omit [Fintype E] in
/-- The number of bits of every partial product is bounded by the input sizes of its factors.
The extra bit covers the empty product. -/
theorem product_size_le (weight : E → ℚ) (s : Finset E) :
    (∏ e ∈ s, (weight e).den).size ≤ (∑ e ∈ s, (weight e).den.size) + 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [Finset.prod_insert he, Finset.sum_insert he]
    exact (size_mul_le_add _ _).trans (by omega)

theorem denominator_size_le (weight : E → ℚ) :
    (denominator weight).size ≤ (∑ e, (weight e).den.size) + 1 :=
  product_size_le weight Finset.univ

theorem qty_size_le (Q : ℕ) (weight : ℚ) :
    (qty Q weight).size ≤ weight.num.natAbs.size + Q.size :=
  (size_mul_le_add _ _).trans (Nat.add_le_add_left (Nat.size_le_size (Nat.div_le_self _ _)) _)

theorem qty_denominator_size_le (weight : E → ℚ) (e : E) :
    (qty (denominator weight) (weight e)).size ≤
      (weight e).num.natAbs.size + ((∑ i, (weight i).den.size) + 1) :=
  (qty_size_le _ _).trans (Nat.add_le_add_left (denominator_size_le weight) _)

end Denominator
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
