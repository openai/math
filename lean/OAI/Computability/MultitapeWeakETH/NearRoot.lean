import OAI.Computability.MultitapeWeakETH.Exponent
import OAI.Computability.MultitapeWeakETH.Main
import OAI.Computability.NearSquareRoot.Main

/-! # Optimal logarithmic exponent for exact integer multiplication -/

namespace OAI.Computability.MultitapeWeakETH

/-- Under Weak ETH, the infimum of the achievable logarithmic exponents for
exact multiplication on a deterministic multitape machine is one half. -/
theorem optimal_exponent_of_weakETH (weak : WeakETH) :
    IsGLB {r | Achievable r} (1 / 2 : ℝ) :=
  optimal_exponent (main_of_weakETH weak) NearSquareRoot.uniformMultiplication

end OAI.Computability.MultitapeWeakETH
