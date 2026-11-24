import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Basic.Real.Basic

/-!
# Contraction bounds for polynomials in tensor generators

In Theorem 2.4 of *VP and VNP differ over every field*, a contraction of
each monomial in the generators satisfies its own target bound. Expanding
the direct sums and tensor powers on the right of the comparison gives a
polynomial with natural coefficients. Subadditivity and the bound for
copies extend the monomial estimates to this whole polynomial.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Spectral

/-- A subadditive function with a bound on copies respects the target
bound for every natural-coefficient polynomial in the generators, provided
it respects the bound on each coefficient-one monomial. -/
theorem polynomial_target_bound {ι S : Type*} [CommSemiring S]
    (Φ : S → ℝ) (G : ι → S) (target : ι → ℝ)
    (hadd : ∀ x y, Φ (x + y) ≤ Φ x + Φ y)
    (hcopies : ∀ (n : ℕ) (x : S), Φ ((n : S) * x) ≤ (n : ℝ) * Φ x)
    (hmonomial : ∀ d : ι →₀ ℕ,
      Φ (d.prod fun i k => G i ^ k) ≤ d.prod fun i k => target i ^ k)
    (p : MvPolynomial ι ℕ) :
    Φ (MvPolynomial.aeval G p) ≤ MvPolynomial.aeval target p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d n =>
    simp only [MvPolynomial.aeval_monomial]
    exact (hcopies n _).trans (mul_le_mul_of_nonneg_left (hmonomial d) n.cast_nonneg)
  | add p q hp hq =>
    simp only [map_add]
    exact (hadd _ _).trans (add_le_add hp hq)

end Spectral

end VPVNP
end Computability
end OAI
