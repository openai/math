import OAI.Optimization.LinearProgramming.PriceGame.ControlWeightFolds
import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel

/-! # Uniform score multipliers for the outer campaign -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- The finite-bit-stack multiplier uses exactly the score cap or the score,
whichever is smaller. The bound therefore also controls malformed inputs. -/
noncomputable def boundedPowerRatP : Procedure (prodCode unaryCode Nat.bits) ratCode
    (fun x => (2 : ℚ) ^ min x.1 x.2) :=
  (natToRat.comp boundedPowerTwoP).congrFun (by intro x; simp)

/-- Physical computation of the public cap on every root expert's score. -/
noncomputable def scoreCapP : Procedure unaryCode unaryCode (fun n => (2*n)^274) :=
  (OracleSpec.Fuel.polynomial (identity unaryCode) ((Polynomial.C 2 * Polynomial.X)^274)).congrFun
    (by intro n; simp)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
