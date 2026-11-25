import Mathlib.Algebra.Polynomial.Eval.Defs

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Campaign

/-- The public formula uses natural coefficients throughout. Keeping the exponents as
arguments lets evaluation use polynomial identities even for the paper's large constants. -/
noncomputable def registerPolynomialAt (timeDegree scoreDegree nprobes rateBits cataloguePower : ℕ) : Polynomial ℕ :=
  let x := (Polynomial.X : Polynomial ℕ)
  let t := x^timeDegree
  let a := (x+t+1) * Polynomial.C cataloguePower
  3 + (t + (x+1) * (Polynomial.C (2*nprobes) * (2*x)^scoreDegree) + Polynomial.C nprobes) +
    2 * ((a+(6+a)*t) + Polynomial.C (rateBits*nprobes))

theorem eval_registerPolynomialAt (timeDegree scoreDegree nprobes rateBits cataloguePower x : ℕ) :
    (registerPolynomialAt timeDegree scoreDegree nprobes rateBits cataloguePower).eval x =
    let t := x ^ timeDegree
    let a := (x + t + 1) * cataloguePower
    3 + (t + (x+1)*((2*nprobes)*(2*x)^scoreDegree)+nprobes) +
      2*((a+(6+a)*t)+rateBits*nprobes) := by
  simp only [registerPolynomialAt, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_ofNat, Polynomial.eval_one]

end Campaign
end PriceGame
end LinearProgramming
end Optimization
end OAI
