import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import Mathlib.Data.Rat.Floor

/-! Fixed finite bit-stack procedures for the scalar instructions of integral LLL.
Integers are encoded in sign/magnitude form; Gram denominators are unsigned binary. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev GramQuad := (ℕ × ℕ) × (ℕ × ℤ)

def gramQuadCode := prodCode (prodCode Nat.bits Nat.bits) (prodCode Nat.bits intCode)

def intTripleCode := prodCode intCode (prodCode intCode intCode)

def gramPairCode := prodCode gramQuadCode (prodCode intCode intCode)

/-- The integer quotient is total even when the encoded denominator is zero. -/
noncomputable def intDivNatP : Procedure (prodCode intCode Nat.bits) intCode
    (fun x : ℤ × ℕ => x.1 / (x.2 : ℤ)) := by
  let a := intToRat.comp (first intCode Nat.bits)
  let d := natToRat.comp (second intCode Nat.bits)
  exact (ratFloor.comp (ratDiv.comp (a.pair d))).congrFun fun x => Rat.floor_intCast_div_natCast x.1 x.2

/-- Nearest quotient with exactly the floor convention of the native reducer. -/
def nearest (x : ℤ × ℕ) : ℤ := (2*x.1 + x.2).fdiv (2 * (x.2 : ℤ))

noncomputable def nearestP : Procedure (prodCode intCode Nat.bits) intCode nearest := by
  let a := first intCode Nat.bits
  let d := second intCode Nat.bits
  let twoA := intMul.comp ((constant _ intCode (2 : ℤ)).pair a)
  let num := intAdd.comp (twoA.pair (natToInt.comp d))
  let den := binaryMul.comp ((constant _ Nat.bits 2).pair d)
  refine (intDivNatP.comp (num.pair den)).congrFun ?_
  intro x
  change (2*x.1 + (x.2 : ℤ)) / ((2*x.2 : ℕ) : ℤ) = _
  rw [nearest, Int.fdiv_eq_ediv_of_nonneg _ (by positivity : 0 ≤ 2*(x.2 : ℤ))]
  push_cast
  rfl

def needsReduction (x : ℤ × ℕ) : Bool := decide (2*x.1.natAbs > x.2)

noncomputable def needsReductionP : Procedure (prodCode intCode Nat.bits) boolCode needsReduction := by
  let d := second intCode Nat.bits
  let mag := intAbs.comp (first intCode Nat.bits)
  let twice := binaryMul.comp ((constant _ Nat.bits 2).pair mag)
  exact binaryLt.comp (d.pair twice)

/-- Row-entry `x − r*y` for the target basis row and each earlier scaled coefficient. -/
def subMul (v : ℤ × (ℤ × ℤ)) : ℤ := v.1 - v.2.1*v.2.2

noncomputable def subMulP : Procedure intTripleCode intCode subMul := by
  let x := first intCode (prodCode intCode intCode)
  let ry := second intCode (prodCode intCode intCode)
  exact intSub.comp (x.pair (intMul.comp ry))

private noncomputable def prevP : Procedure gramQuadCode Nat.bits (fun g : GramQuad => g.1.1) :=
  (first Nat.bits Nat.bits).comp (first (prodCode Nat.bits Nat.bits) (prodCode Nat.bits intCode))

private noncomputable def curP : Procedure gramQuadCode Nat.bits (fun g : GramQuad => g.1.2) :=
  (second Nat.bits Nat.bits).comp (first (prodCode Nat.bits Nat.bits) (prodCode Nat.bits intCode))

private noncomputable def nextP : Procedure gramQuadCode Nat.bits (fun g : GramQuad => g.2.1) :=
  (first Nat.bits intCode).comp (second (prodCode Nat.bits Nat.bits) (prodCode Nat.bits intCode))

private noncomputable def nuP : Procedure gramQuadCode intCode (fun g : GramQuad => g.2.2) :=
  (second Nat.bits intCode).comp (second (prodCode Nat.bits Nat.bits) (prodCode Nat.bits intCode))

/-- The unsigned swap numerator is the sum of a product of Gram determinants and a square. -/
def gramNumerator (g : GramQuad) : ℕ := g.1.1*g.2.1 + g.2.2.natAbs*g.2.2.natAbs

noncomputable def gramNumeratorP : Procedure gramQuadCode Nat.bits gramNumerator := by
  let a := binaryMul.comp (prevP.pair nextP)
  let x := intAbs.comp nuP
  exact binaryAdd.comp (a.pair (binaryMul.comp (x.pair x)))

def lovasz (g : GramQuad) : Bool := decide (3 * (g.1.2*g.1.2) ≤ 4 * gramNumerator g)

noncomputable def lovaszP : Procedure gramQuadCode boolCode lovasz := by
  let lhs := binaryMul.comp ((constant _ Nat.bits 3).pair (binaryMul.comp (curP.pair curP)))
  let rhs := binaryMul.comp ((constant _ Nat.bits 4).pair gramNumeratorP)
  exact binaryLe.comp (lhs.pair rhs)

def swappedGram (g : GramQuad) : ℕ := gramNumerator g / g.1.2

noncomputable def swappedGramP : Procedure gramQuadCode Nat.bits swappedGram :=
  binaryDiv.comp (gramNumeratorP.pair curP)

/-- Both entries of one trailing scaled-coefficient pair in an adjacent swap. -/
def swapPair (x : GramQuad × (ℤ × ℤ)) : ℤ × ℤ :=
  let g := x.1
  let a := x.2.1
  let b := x.2.2
  (((g.1.1 : ℤ)*a + g.2.2*b)/(g.1.2 : ℤ),
    ((g.2.1 : ℤ)*b - g.2.2*a)/(g.1.2 : ℤ))

noncomputable def swapPairP : Procedure gramPairCode (prodCode intCode intCode) swapPair := by
  let g := first gramQuadCode (prodCode intCode intCode)
  let pair := second gramQuadCode (prodCode intCode intCode)
  let a := (first intCode intCode).comp pair
  let b := (second intCode intCode).comp pair
  let prev := (natToInt.comp prevP).comp g
  let nxt := (natToInt.comp nextP).comp g
  let nu := nuP.comp g
  let d := curP.comp g
  let u := intAdd.comp ((intMul.comp (prev.pair a)).pair (intMul.comp (nu.pair b)))
  let v := intSub.comp ((intMul.comp (nxt.pair b)).pair (intMul.comp (nu.pair a)))
  exact (intDivNatP.comp (u.pair d)).pair (intDivNatP.comp (v.pair d))

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
