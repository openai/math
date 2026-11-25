import OAI.Optimization.LinearProgramming.Compression.ProxyFuel
import OAI.Optimization.LinearProgramming.Compression.ParameterPolynomialRAM

/-! Executable ascending coefficients of the manuscript's fixed cutoff polynomial. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

private def addFuelCoefficients : List ℕ → List ℕ → List ℕ
  | [], b => b
  | a::as, [] => a::as
  | a::as, b::bs => (a+b)::addFuelCoefficients as bs

@[local simp] private theorem fuelValue_nil (n : ℕ) : parameterCoefficientValue [] n = 0 := rfl

@[local simp] private theorem fuelValue_cons (a : ℕ) (cs : List ℕ) (n : ℕ) :
    parameterCoefficientValue (a::cs) n = parameterCoefficientValue cs n*n+a := rfl

private theorem fuelValue_add (a b : List ℕ) (n : ℕ) :
    parameterCoefficientValue (addFuelCoefficients a b) n =
      parameterCoefficientValue a n + parameterCoefficientValue b n := by
  induction a generalizing b with
  | nil => simp [addFuelCoefficients]
  | cons c cs ih =>
    cases b with
    | nil => simp [addFuelCoefficients]
    | cons d ds =>
      rw [addFuelCoefficients, fuelValue_cons, ih, fuelValue_cons, fuelValue_cons]
      ring

/-- Multiplication by `n+1` adds the coefficient list to its one-place shift. -/
private def multiplyBySucc : List ℕ → List ℕ
  | [] => []
  | a::as => addFuelCoefficients (a::as) (0::a::as)

private theorem fuelValue_multiplyBySucc (cs : List ℕ) (n : ℕ) :
    parameterCoefficientValue (multiplyBySucc cs) n = parameterCoefficientValue cs n*(n+1) := by
  cases cs with
  | nil => simp [multiplyBySucc]
  | cons c cs =>
    rw [multiplyBySucc, fuelValue_add, fuelValue_cons 0]
    ring

private def addFuelConstant (c : ℕ) : List ℕ → List ℕ
  | [] => [c]
  | a::as => (a+c)::as

private theorem fuelValue_addConstant (c : ℕ) (cs : List ℕ) (n : ℕ) :
    parameterCoefficientValue (addFuelConstant c cs) n = parameterCoefficientValue cs n+c := by
  cases cs <;> simp [addFuelConstant, Nat.add_assoc]

/-- Substitute `(n+1)^3` by Horner evaluation in ascending coefficient lists. -/
private def substituteShiftedCube : List ℕ → List ℕ
  | [] => []
  | a::as => addFuelConstant a (multiplyBySucc (multiplyBySucc (multiplyBySucc (substituteShiftedCube as))))

private theorem fuelValue_substituteShiftedCube (cs : List ℕ) (n : ℕ) :
    parameterCoefficientValue (substituteShiftedCube cs) n = parameterCoefficientValue cs ((n+1)^3) := by
  induction cs with
  | nil => rfl
  | cons a as ih =>
    rw [substituteShiftedCube, fuelValue_addConstant, fuelValue_multiplyBySucc,
      fuelValue_multiplyBySucc, fuelValue_multiplyBySucc, ih, fuelValue_cons]
    ring

/-- In `u=(n+1)^3`, the two parameters of the fuel formula are `w=u²`
and `B=100u`. Expanding that formula gives the following degree-14 polynomial. -/
private def cubicFuelCoefficients : List ℕ :=
  [92039, 781100, 307737, 2590200, 426942, 3509200, 317978, 2509200,
   136684, 1008400, 33170, 216000, 4000, 19200, 160]

/-- A finite, computable coefficient list accepted directly by the initializer RAM. -/
def manuscriptProxyFuelCoefficients : List ℕ := substituteShiftedCube cubicFuelCoefficients

theorem manuscriptProxyFuelCoefficients_length : manuscriptProxyFuelCoefficients.length = 43 := by decide

set_option maxRecDepth 16384 in
theorem manuscriptProxyFuelCoefficients_value (n : ℕ) :
    parameterCoefficientValue manuscriptProxyFuelCoefficients n = manuscriptProxyFuel n := by
  rw [manuscriptProxyFuelCoefficients, fuelValue_substituteShiftedCube]
  unfold manuscriptProxyFuel manuscriptProxyFuelFormula
  dsimp only
  rw [show (n+1)^6 = ((n+1)^3)^2 by ring]
  generalize (n+1)^3 = u
  simp only [cubicFuelCoefficients, fuelValue_cons, fuelValue_nil, proxyRoundingInputFormula,
    proxyQueryWidthFormula]
  ring

end Compression
end LinearProgramming
end Optimization
end OAI
