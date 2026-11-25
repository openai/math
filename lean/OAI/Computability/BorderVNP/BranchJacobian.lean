import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The separable deformation in Proposition 9.2

The slice equations are deformed by adding `t (zᵢ - vᵢ)`. Over the function field of the
parameter chart this adds a scalar matrix to the Jacobian, so its determinant is monic
in the independent variable `t`, including in positive characteristic. On the chart
where the denominator is nonzero, clearing it preserves nonsingularity at a common zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial
open scoped Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Matrix of the parameter partial derivatives of a square system evaluated at a point. -/
noncomputable def jacobianAt (f : ι → MvPolynomial ι K) (z : ι → K) : Matrix ι ι K :=
  Matrix.of fun i j => eval z (pderiv j (f i))

/-- The deformed polynomial equations in (9.1) at parameter value `t`. -/
noncomputable def deformed (f : ι → MvPolynomial ι K) (v : ι → K) (t : K) :
    ι → MvPolynomial ι K :=
  fun i => f i + C t * (X i - C (v i))

/-- The deformation adds `tI` to the Jacobian of the undeformed slices. -/
theorem jacobianAt_deformed (f : ι → MvPolynomial ι K) (v z : ι → K) (t : K) :
    jacobianAt (deformed f v t) z = Matrix.scalar ι t + jacobianAt f z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [jacobianAt, deformed, Matrix.scalar, add_comm]
  · simp [jacobianAt, deformed, Matrix.scalar, hij]

/-- The determinant of the Jacobian pencil `tI + A` is a monic polynomial of degree
the number of parameters. This applies directly with `K` the function field and `A`
the matrix of the rational-chart derivatives. -/
theorem determinant_pencil (A : Matrix ι ι K) :
    ∃ p : Polynomial K, p.Monic ∧ p.natDegree = Fintype.card ι ∧
      ∀ t, p.eval t = (Matrix.scalar ι t + A).det := by
  refine ⟨(-A).charpoly, Matrix.charpoly_monic _, Matrix.charpoly_natDegree_eq_dim _, ?_⟩
  intro t
  rw [Matrix.eval_charpoly, sub_neg_eq_add]

/-- In the generic deformation the polynomial determinant itself is nonzero.
No separability hypothesis on the original slices is required. -/
theorem determinant_generic_ne_zero (A : Matrix ι ι K) :
    (Matrix.scalar ι (Polynomial.X : Polynomial K) +
      (Polynomial.C : K →+* Polynomial K).mapMatrix A).det ≠ 0 := by
  convert (-A).charpoly_monic.ne_zero using 1
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.map_neg Polynomial.C (map_neg Polynomial.C) A]

omit [Fintype ι] [DecidableEq ι] in
/-- Multiplication by a common chart denominator scales each Jacobian row by its
value at a common zero. -/
theorem jacobianAt_cleared (f : ι → MvPolynomial ι K) (den : MvPolynomial ι K)
    (z : ι → K) (hz : ∀ i, eval z (f i) = 0) :
    jacobianAt (fun i => den * f i) z = eval z den • jacobianAt f z := by
  ext i j
  simp [jacobianAt, hz]

/-- At a common zero in the chart, clearing the denominator preserves invertibility
of the Jacobian in both directions. -/
theorem determinant_cleared_ne_zero_iff (f : ι → MvPolynomial ι K) (den : MvPolynomial ι K)
    (z : ι → K) (hz : ∀ i, eval z (f i) = 0) (hd : eval z den ≠ 0) :
    (jacobianAt (fun i => den * f i) z).det ≠ 0 ↔ (jacobianAt f z).det ≠ 0 := by
  rw [jacobianAt_cleared f den z hz, Matrix.det_smul, mul_ne_zero_iff]
  simp [hd]

end Branch

end BorderVNP
end Computability
end OAI
