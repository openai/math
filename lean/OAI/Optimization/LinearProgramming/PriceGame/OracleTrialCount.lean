import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPad

/-! Compute the trial count in the actual PCG algorithm. Public N, R and anchor are
provided in binary. Only N has already been expanded by the native dimension bootstrap. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open OAI.Optimization.LinearProgramming.OracleSpec
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

noncomputable def publicFieldsP : Procedure eiPad (prodCode Nat.bits (prodCode Nat.bits Nat.bits))
    (fun i => (i.goods, i.range, i.anchor.val)) := by
  let raw : Procedure eiPad Wire.inputWire (fun i : PublicInput => (i.goods, i.range, i.anchor.val)) :=
    publicInputP.result (by intro i; rfl)
  exact Wire.parseInput.comp raw

noncomputable def sourceInputSizeP : Procedure eiPad unaryCode (fun i => i.goods+i.range.size+1) := by
  let n : Procedure eiPad unaryCode PublicInput.goods := unaryGoodsP.result (by intro i; rfl)
  let tail := (second Nat.bits (prodCode Nat.bits Nat.bits)).comp publicFieldsP
  let r := (first Nat.bits Nat.bits).comp tail
  let len := (Fuel.lengthInUnary Nat.bits).comp r
  let total := unaryAdd.comp (n.pair len)
  exact (unarySuccessor.comp total).congrFun (by intro i; simp [Nat.size_eq_bits_len])

/-- The paper first computes a fixed power of its public dimension/bit-length parameter.
The exponent is part of the program, and no oracle is used in this phase. -/
noncomputable def sourcePowerUnaryP (k : ℕ) : Procedure eiPad unaryCode
    (fun i => (i.goods+i.range.size+1)^k) :=
  (Fuel.polynomial sourceInputSizeP (Polynomial.X ^ k)).congrFun (by intro i; simp)

noncomputable def sourcePowerBinaryP (k : ℕ) : Procedure eiPad Nat.bits
    (fun i => (i.goods+i.range.size+1)^k) := unaryToBits.comp (sourcePowerUnaryP k)

/-- The fixed choice in the Section 7 campaign bound, ready for the outer loop and its
serialized counter. -/
noncomputable def trialCountUnaryP := sourcePowerUnaryP 300
noncomputable def trialCountBinaryP := sourcePowerBinaryP 300

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
