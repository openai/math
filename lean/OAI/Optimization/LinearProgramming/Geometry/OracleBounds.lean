import Mathlib.Algebra.Polynomial.Eval.Defs
import OAI.Optimization.LinearProgramming.Geometry.OracleConcreteBounds

/-! Polynomial bounds for repeated geometric label calls in the full recovery machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace LabelRAM

open RAM

/-- Fixed natural polynomial for a complete call to the live label routine. -/
noncomputable def labelTimePolynomial : Polynomial ℕ :=
  Polynomial.C 510006600 * (Polynomial.X+1)^9

private theorem eval_bound_polynomial (c degree x : ℕ) :
    (Polynomial.C c * (Polynomial.X + 1)^degree : Polynomial ℕ).eval x = polyBound c degree x := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, polyBound]

/-- Keep a polynomial together with its exact formula and pointwise evaluation. -/
@[irreducible] private noncomputable def certifiedBoundPolynomial (c degree : ℕ) :
    {p : Polynomial ℕ // p = Polynomial.C c * (Polynomial.X+1)^degree ∧
      ∀ x, p.eval x = polyBound c degree x} :=
  ⟨Polynomial.C c * (Polynomial.X+1)^degree, rfl, eval_bound_polynomial c degree⟩

/-- The maximum increase over the caller's current scalar-register width. -/
noncomputable def labelWidthPolynomial : Polynomial ℕ :=
  (certifiedBoundPolynomial concreteWidthCoefficient 315).1

theorem labelWidthPolynomial_formula :
    labelWidthPolynomial = Polynomial.C concreteWidthCoefficient * (Polynomial.X+1)^315 :=
  (certifiedBoundPolynomial concreteWidthCoefficient 315).2.1

private theorem labelWidthPolynomial_eval (x : ℕ) :
    labelWidthPolynomial.eval x = polyBound concreteWidthCoefficient 315 x :=
  (certifiedBoundPolynomial concreteWidthCoefficient 315).2.2 x

theorem concreteTime_le_eval (r n : ℕ) :
    time r n (BorderBatch.batchTime r n) ≤ labelTimePolynomial.eval (r+n) := by
  simpa only [labelTimePolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,polyBound] using concreteTime_bound r n

private theorem transfer_add_bound {w H b u : ℕ} (h : w ≤ H+b) (e : u = b) : w ≤ H+u :=
  h.trans_eq (congrArg (Nat.add H) e.symm)

set_option maxRecDepth 8000 in
theorem concreteWidth_le_eval (r n e g H : ℕ) :
    width r n (BorderBatch.batchLocalWidth n e g) (BorderBatch.batchIncrement n e g) H ≤
      H+labelWidthPolynomial.eval (r+n+e+g) :=
  @transfer_add_bound
    (width r n (BorderBatch.batchLocalWidth n e g) (BorderBatch.batchIncrement n e g) H) H
    (polyBound concreteWidthCoefficient 315 (r+n+e+g)) (labelWidthPolynomial.eval (r+n+e+g))
    (concreteWidth_bound r n e g H) (labelWidthPolynomial_eval (r+n+e+g))

end LabelRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
