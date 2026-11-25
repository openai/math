import OAI.Computability.BorderVNP.ResidueLaurentJet

/-! # The branch derivative in the Taylor jet

The Laurent derivative of each q-th power vanishes. The finite Frobenius
expansion then identifies the jet of the branch derivative with the formal
derivative of the jet in its nilpotent variable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue

open HahnSeries
open scoped LaurentSeries

variable {K : Type*} [Field K] (p u : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- The derivative with respect to the Laurent parameter has coefficient
(k+1) a_{k+1} at k, also for negative k. -/
theorem laurentDerivative_coeff (D : LaurentSeries K) (k : ℤ) :
    (LaurentSeries.derivative K D).coeff k = ((k + 1 : ℤ) : K) * D.coeff (k + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  simp [zsmul_eq_mul]

private theorem parameterTerm_coeff (r : ℕ) (V : LaurentSeries K) (k : ℤ) :
    (parameter K ^ r * V).coeff k = V.coeff (k - r) := by
  rw [parameter, single_pow, coeff_single_mul]
  simp

omit [PerfectRing K p] in
/-- The derivative differentiates the power of s and kills every q-th power. -/
theorem laurentDerivative_term (hu : 0 < u) (r : ℕ) (U : LaurentSeries K) :
    LaurentSeries.derivative K (parameter K ^ r * U ^ p ^ u) =
      r • (parameter K ^ (r - 1) * U ^ p ^ u) := by
  ext k
  rw [laurentDerivative_coeff, parameterTerm_coeff, coeff_smul, nsmul_eq_mul, parameterTerm_coeff]
  by_cases h : ((p ^ u : ℕ) : ℤ) ∣ k + 1 - r
  · obtain ⟨j, hj⟩ := h
    have hz : ((k + 1 : ℤ) : K) = (r : K) := by
      have hcast := congrArg (fun x : ℤ => (x : K)) hj
      push_cast at hcast ⊢
      rw [CharP.cast_eq_zero K p, zero_pow hu.ne', zero_mul] at hcast
      exact sub_eq_zero.mp hcast
    rw [hz]
    by_cases hr : r = 0
    · simp [hr]
    · rw [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one, show k + 1 - r = k - (r - 1) by ring]
  · rw [coeff_pow_frobenius_of_not_dvd p u _ _ h, mul_zero]
    by_cases hr : r = 0
    · simp [hr]
    · rw [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one, show k - (r - 1) = k + 1 - r by ring,
        coeff_pow_frobenius_of_not_dvd p u _ _ h, mul_zero]

variable {R : Type*} [CommRing R] [ExpChar R p]

/-- Differentiating the polynomial representative before substitution agrees with
substituting in the Laurent derivative, for any nilpotent perturbation of order q. -/
theorem eval_jetPolynomial_derivative (hu : 0 < u) (f : LaurentSeries K →+* R)
    (δ : R) (hδ : δ ^ p ^ u = 0) (D : LaurentSeries K) :
    (jetPolynomial p u D).derivative.eval₂ f δ =
      taylorJet p u f δ hδ (LaurentSeries.derivative K D) := by
  rw [jetPolynomial, Polynomial.derivative_sum, Polynomial.eval₂_finsetSum]
  conv_rhs => rw [← sum_sections p u D]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_add_C_pow, laurentDerivative_term p u hu,
    map_nsmul, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C]
  rw [Polynomial.eval₂_C]
  change f (_ ^ p ^ u) * (f r * (δ + f (parameter K)) ^ (r - 1)) =
    r • jetHom p u f (f (parameter K) + δ) _ (parameter K ^ (r - 1) * _ ^ p ^ u)
  rw [jetHom_term, nsmul_eq_mul, map_natCast, add_comm]
  ring

/-- The value of a Taylor jet at zero is the given Laurent series. -/
theorem taylorJet_zero (f : LaurentSeries K →+* R) (D : LaurentSeries K) :
    taylorJet p u f 0 (zero_pow (expChar_pow_pos K p u).ne') D = f D := by
  change ∑ r ∈ Finset.range _, (f (parameter K) + 0) ^ r * f (sectionSeries p u r D ^ p ^ u) = _
  simpa only [map_sum, map_mul, map_pow, add_zero] using congrArg f (sum_sections p u D)

/-- The coefficient of degree one in the jet gives the Laurent derivative. -/
theorem jetPolynomial_coeff_one (hu : 0 < u) (D : LaurentSeries K) :
    (jetPolynomial p u D).coeff 1 = LaurentSeries.derivative K D := by
  have : ExpChar (LaurentSeries K) p :=
    expChar_of_injective_ringHom (f := HahnSeries.C) HahnSeries.C_injective p
  have h := eval_jetPolynomial_derivative p u hu (RingHom.id (LaurentSeries K)) 0
    (zero_pow (expChar_pow_pos K p u).ne') D
  rw [taylorJet_zero] at h
  simpa [← Polynomial.eval₂_at_apply, Polynomial.coeff_derivative] using h

end Residue

end BorderVNP
end Computability
end OAI
