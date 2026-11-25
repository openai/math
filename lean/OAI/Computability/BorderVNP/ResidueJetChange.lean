import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.CharP.Basic

/-!
# Reparametrizing the top coefficient of a differential jet

At characteristic `p` a jet substitution with zero constant coefficient
transforms the coefficient of degree `p−1` of a differential by the
`p`-th power of the linear coefficient.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open Polynomial

variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]

private theorem top_monomial_change (T : K[X]) (hT : T.coeff 0 = 0) (j : ℕ) :
    (T ^ j * T.derivative).coeff (p - 1) =
      if j = p - 1 then (T.coeff 1) ^ p else 0 := by
  have hp := (Fact.out : p.Prime).pos
  have hd : p - 1 + 1 = p := Nat.sub_add_cancel hp
  rcases lt_trichotomy j (p - 1) with hj | rfl | hj
  · rw [ite_eq_right hj.ne]
    have hn : ((j+1 : ℕ) : K) ≠ 0 := by
      intro hj0
      exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos _) (by omega : j+1 < p)
        ((CharP.cast_eq_zero_iff K p _).mp hj0)
    have h := coeff_derivative (T ^ (j+1)) (p-1)
    rw [← Nat.cast_succ, Nat.succ_eq_add_one, hd, CharP.cast_eq_zero K p, mul_zero, derivative_pow, Nat.add_sub_cancel,
      mul_assoc, coeff_C_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hn
  · obtain ⟨B, rfl⟩ := X_dvd_iff.mpr hT
    rw [ite_eq_left rfl, mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
    have hB : (X * B).coeff 1 = B.coeff 0 := by simp
    rw [hB, coeff_zero_eq_eval_zero, eval_mul, eval_pow, ← coeff_zero_eq_eval_zero,
      ← coeff_zero_eq_eval_zero, coeff_derivative, hB]
    simp [← pow_succ, hd]
  · obtain ⟨B, rfl⟩ := X_dvd_iff.mpr hT
    rw [ite_eq_right hj.ne', mul_pow, mul_assoc, coeff_X_pow_mul', ite_eq_right hj.not_ge]

/-- Substituting a local parameter in a differential preserves its top jet coefficient
up to the Frobenius of the Jacobian, even for a nonlinear substitution. -/
theorem top_jet_change (P T : K[X]) (hT : T.coeff 0 = 0) :
    ((P.comp T) * T.derivative).coeff (p - 1) = P.coeff (p-1) * (T.coeff 1)^p := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [add_mul, hP, hQ]
  | monomial j a =>
    rw [monomial_comp, mul_assoc, coeff_C_mul, top_monomial_change p T hT, coeff_monomial]
    by_cases h : j = p - 1 <;> simp [h]

end Residue

end BorderVNP
end Computability
end OAI
