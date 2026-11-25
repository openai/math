import OAI.Optimization.LinearProgramming.Lattice.BitState
import OAI.Optimization.LinearProgramming.Lattice.QueryWire
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding
import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel

/-! Finite binary-stack instructions for the actual sign-oracle request, response,
and the two size-dependent parameters of a rounding invocation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open OracleSpec

def signedField (z : ℤ) : Word := decide (z < 0) :: encodeNat z.natAbs

noncomputable def signedFieldP : Procedure intCode id signedField := by
  let sign : Procedure intCode id (fun z : ℤ => [decide (z < 0)]) :=
    intSign.result (fun _ => rfl)
  exact (append.comp (sign.pair (Wire.writeNat.comp intAbs))).congrFun (fun _ => rfl)

def signPacket (a : List ℤ) : Word := a.flatMap signedField

noncomputable def signPacketP : Procedure intRowCode id signPacket :=
  (Wire.flatten.comp (listMap (0:ℤ) ([]:Word) signedFieldP)).congrFun (fun _ => rfl)

theorem signPacket_pack {p : ℕ} (a : Fin p → ℤ) : signPacket (List.ofFn a) = signRowWord a := rfl

def nonnegativeAnswer (w : Word) : Bool := w.headD false || w.tail.headD false

noncomputable def nonnegativeAnswerP : Procedure id boolCode nonnegativeAnswer :=
  boolOr.comp (head.pair (head.comp tail))

theorem nonnegativeAnswer_sign (s : Ordering) :
    nonnegativeAnswer (signReply s) = decide (s ≠ .lt) := by cases s <;> rfl

/-- The dimension has a unary representation so all dimension-indexed loops in
this one machine are polynomial in the physical argument. The radius is binary. -/
abbrev Input := ℕ × ℕ

def inputCode : Input → Word := prodCode unaryCode Nat.bits

noncomputable def precisionExponentP : Procedure inputCode unaryCode
    (fun x : Input => precisionExponent x.1 x.2) := by
  let p := first unaryCode Nat.bits
  let width := (Fuel.lengthInUnary Nat.bits).comp (second unaryCode Nat.bits)
  let four := unaryMul.comp ((constant inputCode unaryCode 4).pair (unarySuccessor.comp p))
  exact (unaryAdd.comp ((unaryAdd.comp (four.pair width)).pair
    (constant inputCode unaryCode 6))).congrFun (by intro; simp [precisionExponent,Nat.size_eq_bits_len])

noncomputable def searchPrecisionP : Procedure inputCode unaryCode
    (fun x : Input => searchPrecision x.1 x.2) := by
  let p := first unaryCode Nat.bits
  let two := unarySuccessor.comp (unarySuccessor.comp p)
  exact (unaryMul.comp (precisionExponentP.pair two)).congrFun (fun _ => rfl)

noncomputable def radixWidthP : Procedure inputCode unaryCode (fun x : Input => radixWidth x.1 x.2) := by
  let p := first unaryCode Nat.bits
  let width := (Fuel.lengthInUnary Nat.bits).comp (second unaryCode Nat.bits)
  let block := unaryMul.comp (precisionExponentP.pair (unarySuccessor.comp p))
  exact (unaryAdd.comp ((unaryAdd.comp (width.pair block)).pair
    (constant inputCode unaryCode 3))).congrFun (by intro; simp [radixWidth,Nat.size_eq_bits_len])

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
