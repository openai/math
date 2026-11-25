import OAI.ThreeFlat.Diagonal.DefectBudget
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Tactic.Ring

namespace OAI
/-! # Fixed-width address bounds for the native trace

At diagonal scale `u` the RAM has `16*u^10` bits per word. A trace with
`2^d` rows can use a fixed polynomial number of words per row and still
address them all. The word threshold depends only on the coefficients and
degree of that polynomial.
-/

namespace ThreeFlat.RAM

/-- A computable scale sufficient for coefficient `c` and degree `k`. -/
def traceWordThreshold (c k : ℕ) : ℕ := max 17 (max c (11*k+1))

private theorem rowPolynomial_le {u c k : ℕ} (hu : traceWordThreshold c k ≤ u) :
    c * (16*u^10+1)^k ≤ 2^(u^2) := by
  have h17 : 17 ≤ u := (le_max_left ..).trans hu
  have hc : c ≤ u := (le_max_left c (11*k+1)).trans ((le_max_right ..).trans hu)
  have hk : 11*k+1 ≤ u := (le_max_right c (11*k+1)).trans ((le_max_right ..).trans hu)
  have hp : 0 < u^10 := Nat.pow_pos (by omega)
  have hwidth : 16*u^10+1 ≤ u^11 := by
    rw [pow_succ u 10]
    have h := Nat.mul_le_mul_left (u^10) h17
    omega
  calc
    c * (16*u^10+1)^k ≤ u * (u^11)^k :=
      Nat.mul_le_mul hc (Nat.pow_le_pow_left hwidth _)
    _ = u^(11*k+1) := by rw [← pow_mul, pow_succ, Nat.mul_comm]
    _ ≤ _ := Diagonal.width_pow_le_two_pow_sq hk

/-- The size of every row, the number of rows, and one extra row of
padding have room below the native word modulus. -/
theorem trace_word_budget_lt {u d c k : ℕ} (hu : traceWordThreshold c k ≤ u)
    (hd : d ≤ 15*u^10) :
    (2^d+1) * (c * (16*u^10+1)^k) < 2^(16*u^10) := by
  have h17 : 17 ≤ u := (le_max_left ..).trans hu
  have hs : 2 ≤ u^2 := (by omega : 2 ≤ u).trans (Nat.le_self_pow (by decide) u)
  have h3 : u^2+2 ≤ u^3 := by
    have h := Nat.mul_le_mul_left (u^2) (by omega : 2 ≤ u)
    rw [pow_succ u 2]
    omega
  have h10 := h3.trans (Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 3 ≤ 10))
  calc
    (2^d+1) * (c * (16*u^10+1)^k) ≤ (2^d+2^d) * 2^(u^2) :=
      Nat.mul_le_mul (by have := Nat.two_pow_pos d; omega) (rowPolynomial_le hu)
    _ = 2^(d+u^2+1) := by rw [pow_succ, pow_add]; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

/-- Substitute arbitrary public row and control counts, a fixed common
coefficient, and a fixed implementation multiplier into the same strict bound. -/
theorem trace_word_address_lt {u d c k a row control address : ℕ}
    (hu : traceWordThreshold (a*c) k ≤ u) (hd : d ≤ 15*u^10)
    (hrow : row ≤ c * (16*u^10+1)^k) (hcontrol : control ≤ c * (16*u^10+1)^k)
    (haddr : address ≤ a * (2^d * row + control)) : address < 2^(16*u^10) := by
  apply lt_of_le_of_lt haddr
  apply lt_of_le_of_lt _ (trace_word_budget_lt hu hd)
  calc
    a * (2^d * row + control) ≤ a * (2^d*(c*(16*u^10+1)^k) + c*(16*u^10+1)^k) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul_left _ hrow) hcontrol)
    _ = _ := by ring

/-- A nonnegative polynomial is bounded by its total coefficient mass at
one times the indicated power of the argument plus one. -/
theorem trace_polynomial_envelope (P : Polynomial ℕ) (x : ℕ) :
    P.eval x ≤ P.eval 1 * (x+1)^P.natDegree := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum]
  simp only [one_pow, mul_one, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ _) _).trans
    (Nat.pow_le_pow_right (by omega) (Polynomial.le_natDegree_of_mem_supp i hi)))

/-- An executable large-word threshold for two concrete public polynomials. -/
theorem trace_word_polynomials_lt (P Q : Polynomial ℕ) (a : ℕ) {u d : ℕ}
    (hu : traceWordThreshold (a * max (P.eval 1) (Q.eval 1)) (max P.natDegree Q.natDegree) ≤ u)
    (hd : d ≤ 15*u^10) :
    a * (2^d * P.eval (16*u^10) + Q.eval (16*u^10)) < 2^(16*u^10) := by
  apply trace_word_address_lt hu hd _ _ le_rfl
  · exact (trace_polynomial_envelope P _).trans (Nat.mul_le_mul (le_max_left ..)
      (Nat.pow_le_pow_right (by omega) (le_max_left ..)))
  · exact (trace_polynomial_envelope Q _).trans (Nat.mul_le_mul (le_max_right ..)
      (Nat.pow_le_pow_right (by omega) (le_max_right ..)))

end ThreeFlat.RAM

end OAI
