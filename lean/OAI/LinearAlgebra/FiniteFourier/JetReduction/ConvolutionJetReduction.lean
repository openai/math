import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

/-! # Monic reduction by two fixed-operand convolutions

For a monic degree-`e` polynomial, a dividend of degree below `2e` can be
reduced using two length-`e` truncated products. Both fixed operands are
polynomials over the original coefficient ring, including over the integers.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace JetReduction

open Polynomial
open scoped PowerSeries

noncomputable section
variable {R : Type*} [CommRing R]

/-- The first `e` coefficients. -/
def low (e : ℕ) (p : R[X]) : R[X] := PowerSeries.trunc e (p : R⟦X⟧)

/-- The reversed high half of a dividend of length `2e`. -/
def highRev (e : ℕ) (p : R[X]) : R[X] := low e (p.reflect (e + (e - 1)))

/-- Precomputed reciprocal of the reversed modulus to precision `e`.
The reversed polynomial has constant coefficient one when the modulus is monic
of degree `e`. -/
def reciprocal (e : ℕ) (m : R[X]) : R[X] :=
  PowerSeries.trunc e (PowerSeries.invOfUnit (m.reflect e : R⟦X⟧) 1)

/-- The Euclidean quotient reconstructed from one length-`e` convolution. -/
def quotient (e : ℕ) (m y : R[X]) : R[X] :=
  (low e (reciprocal e m * highRev e y)).reflect (e - 1)

/-- The low half of the dividend, corrected by one further length-`e`
convolution with the low half of the modulus. -/
def reduce (e : ℕ) (m y : R[X]) : R[X] :=
  low e y - low e (low e m * quotient e m y)

theorem natDegree_low_lt {e : ℕ} (he : 0 < e) (p : R[X]) : (low e p).natDegree < e := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  exact PowerSeries.natDegree_trunc_lt _ n

theorem natDegree_reciprocal_lt {e : ℕ} (he : 0 < e) (m : R[X]) :
    (reciprocal e m).natDegree < e := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  exact PowerSeries.natDegree_trunc_lt _ n

/-- Correctness of the reversed quotient over a commutative coefficient ring. -/
theorem quotient_eq_divByMonic {e : ℕ} (he : 0 < e) {m : R[X]}
    (hm : m.Monic) (hd : m.natDegree = e) (y : R[X]) (hy : y.natDegree < 2 * e) :
    quotient e m y = y /ₘ m := by
  nontriviality R
  let q := y /ₘ m
  let r := y %ₘ m
  have hq : q.natDegree ≤ e - 1 := by
    dsimp [q]; rw [natDegree_divByMonic y hm, hd]; omega
  have hr : r.natDegree < e := by
    have hm1 : m ≠ 1 := fun h ↦ by simp [h] at hd; omega
    exact (natDegree_modByMonic_lt y hm hm1).trans_eq hd
  let f : R⟦X⟧ := (m.reflect e : R[X])
  have hf : f.constantCoeff = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    change PowerSeries.coeff 0 (m.reflect e : R⟦X⟧) = 1
    rw [Polynomial.coeff_coe, coeff_reflect, revAt_zero, ← hd, hm.coeff_natDegree]
  have hrem : highRev e r = 0 := by
    ext k
    simp only [highRev, low, PowerSeries.coeff_trunc, Polynomial.coeff_coe, coeff_reflect,
      Polynomial.coeff_zero]
    split_ifs with hk
    · rw [revAt_le (by omega)]
      exact coeff_eq_zero_of_natDegree_lt (by omega)
    · rfl
  have hhigh : highRev e y = PowerSeries.trunc e (f * (q.reflect (e - 1) : R⟦X⟧)) := by
    conv_lhs => rw [← modByMonic_add_div y m]
    change low e ((r + m * q).reflect (e + (e - 1))) = _
    rw [reflect_add, reflect_mul _ _ hd.le hq, low, Polynomial.coe_add, map_add,
      show PowerSeries.trunc e (r.reflect (e + (e - 1)) : R⟦X⟧) = 0 from hrem,
      zero_add, Polynomial.coe_mul]
  have hqr : (q.reflect (e - 1)).natDegree < e :=
    natDegree_reflect_le.trans_lt (max_lt (by omega) (by omega))
  unfold quotient
  rw [low, Polynomial.coe_mul, reciprocal, PowerSeries.trunc_trunc_mul, hhigh,
    PowerSeries.trunc_mul_trunc, ← mul_assoc, PowerSeries.invOfUnit_mul _ 1 hf,
    one_mul, PowerSeries.trunc_coe_eq_self hqr, reflect_reflect]

/-- The two length-`e` convolutions give the Euclidean remainder. -/
theorem reduce_eq_modByMonic {e : ℕ} (he : 0 < e) {m : R[X]} (hm : m.Monic)
    (hd : m.natDegree = e) (y : R[X]) (hy : y.natDegree < 2 * e) :
    reduce e m y = y %ₘ m := by
  nontriviality R
  have hm1 : m ≠ 1 := fun h ↦ by simp [h] at hd; omega
  have hr : (y %ₘ m).natDegree < e := (natDegree_modByMonic_lt y hm hm1).trans_eq hd
  rw [reduce, quotient_eq_divByMonic he hm hd y hy]
  simp only [low, Polynomial.coe_mul, PowerSeries.trunc_trunc_mul]
  rw [← Polynomial.coe_mul, ← map_sub, ← Polynomial.coe_sub, ← modByMonic_eq_sub_mul_div,
    PowerSeries.trunc_coe_eq_self hr]

/-- All four convolution inputs satisfy the common length bound. -/
theorem operand_degrees {e : ℕ} (he : 0 < e) (m y : R[X]) :
    (reciprocal e m).natDegree < e ∧ (highRev e y).natDegree < e ∧
      (low e m).natDegree < e ∧ (quotient e m y).natDegree < e := by
  refine ⟨natDegree_reciprocal_lt he _, natDegree_low_lt he _, natDegree_low_lt he _, ?_⟩
  exact natDegree_reflect_le.trans_lt (max_lt (by omega) (natDegree_low_lt he _))

end
end JetReduction

end FiniteFourier
end LinearAlgebra
end OAI
