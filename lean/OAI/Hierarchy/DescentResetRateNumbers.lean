import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Scalar parameters of the physical reset menu -/

namespace Hierarchy.DescentColonies
noncomputable section

/-- The estimator coefficient multiplying the sum of allocated base capacities. -/
def resetTail (f : ℕ) : ℝ :=
  let r := (2:ℝ)^(1/8:ℝ)
  ((2:ℝ)^f)^(-(7/8):ℝ) * (1/(r-1)+1/(1-r/2))

end
end Hierarchy.DescentColonies

namespace Hierarchy.DescentResetInvoice
noncomputable section

/-- Two nonhub endpoint directories give a core route with a bound depending
only on Δ and the number of rotor rows. The extra three also cover the roots
and connecting cable in the explicit two-tree implementation. -/
def nonhubHops (Δ Y : ℕ) : ℕ := 72*Nat.clog 2 (2*Δ*Y)+3

end
end Hierarchy.DescentResetInvoice

namespace Hierarchy.DescentCompiler
noncomputable section

def reserveGain (h C f : ℕ) := f+Nat.clog 2 (max 19 (6*(2+21*((2*h+4)*(2*h*C+2)))+1))

end
end Hierarchy.DescentCompiler

namespace Hierarchy.DescentSixParty.ResetInput
noncomputable section

/-- Fixed per-round exponent independent of how many old blocks are grouped. -/
def resetHostGain (h Y height : ℕ) := Nat.clog 2 (4*((Y+1)+((2*h+4)*Y+(Y+1)*2^(height+1))))

end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentMixedRouter
noncomputable section

def rotorRate (h C₀ : ℕ) : ℝ := 21*((2*h+4)*(2*h*C₀+2):ℕ)

end
end Hierarchy.DescentMixedRouter

end OAI
