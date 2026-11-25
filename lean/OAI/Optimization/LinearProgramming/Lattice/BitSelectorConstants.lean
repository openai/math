import OAI.Optimization.LinearProgramming.Lattice.BitTables
import OAI.Optimization.LinearProgramming.Lattice.Precision
import OAI.Optimization.LinearProgramming.OracleSpec.PolynomialFuel
import OAI.Computability.QuantumFactoring.BitStackRationalDivision

/-! Exact graph-lattice constants from a binary radius and a framed rational vector. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Selector
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Input := ℕ × List ℚ

def vectorCode := listCode ratCode
def inputCode := prodCode Nat.bits vectorCode
def outputCode := prodCode Nat.bits intRowCode

def graphAlpha (x : Input) : ℚ :=
  1 / (searchDenominator x.2.length x.1 : ℚ) ^ (x.2.length+1)

def graphScale (x : Input) : ℕ := (graphAlpha x).den * (x.2.map Rat.den).prod

private theorem multiply_length (xs : List ℕ) (b : ℕ) :
    ((xs.foldl (fun a k => k*a) b).bits).length ≤ (listCode Nat.bits xs).length+b.bits.length := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,listCode_length_cons]
    have h := ih (x*b)
    have hm := bits_length_mul x b
    omega

private theorem multiply_value (xs : List ℕ) (b : ℕ) :
    xs.foldl (fun a k => k*a) b = xs.prod*b := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.prod_cons]; ac_rfl

/-- Fold binary multiplication over the actual framed inputs. At any prefix the accumulator
length is at most the sum of input lengths and its original length. -/
noncomputable def natProductP : Procedure (listCode Nat.bits) Nat.bits (List.prod : List ℕ → ℕ) := by
  let fold := foldList 0 binaryMul Polynomial.X (by
    intro xs b i
    simpa only [Polynomial.eval_X] using
      (multiply_length (xs.take i) b).trans
        (Nat.add_le_add_right (listCode_length_take_le Nat.bits i xs) _))
  exact (fold.comp ((identity (listCode Nat.bits)).pair (constant (listCode Nat.bits) Nat.bits 1))).congrFun
    (by intro xs; change xs.foldl (fun b k => k*b) 1 = xs.prod; rw [multiply_value,mul_one])

private theorem double_iter (n a : ℕ) : ((fun b : ℕ => 2*b)^[n]) a = 2^n*a := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ']; exact (Nat.mul_assoc ..).symm

/-- The clock is unary and the result is binary. The intermediate binary length grows by
at most two at each executed doubling. -/
noncomputable def powTwoP : Procedure unaryCode Nat.bits (fun b => 2^b) := by
  let double := binaryMul.comp ((constant Nat.bits Nat.bits 2).pair (identity Nat.bits))
  let loop := double.iterateLinear 2 (by
    intro a
    change (2*a).bits.length ≤ a.bits.length+2
    have h₂ : (2:ℕ).bits.length = 2 := by decide
    simpa [h₂,Nat.add_comm] using bits_length_mul 2 a)
  exact (loop.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 1))).congrFun
    (by intro n; change ((fun b : ℕ => 2*b)^[n]) 1 = _; rw [double_iter,mul_one])

noncomputable def rankP : Procedure inputCode unaryCode (fun x : Input => x.2.length+1) :=
  unarySuccessor.comp ((PriceGame.Control.Native.rowSizeP ratCode 0).comp (second Nat.bits vectorCode))

noncomputable def exponentP : Procedure inputCode unaryCode
    (fun x : Input => precisionExponent x.2.length x.1 * (x.2.length+1)) := by
  let width := (OracleSpec.Fuel.lengthInUnary Nat.bits).comp (first Nat.bits vectorCode)
  let four := unaryMul.comp ((constant inputCode unaryCode 4).pair rankP)
  let sum := unaryAdd.comp (four.pair width)
  let whole := unaryAdd.comp (sum.pair (constant inputCode unaryCode 6))
  exact (unaryMul.comp (whole.pair rankP)).congrFun
    (by intro x; simp [precisionExponent,Nat.size_eq_bits_len])

noncomputable def graphAlphaP : Procedure inputCode ratCode graphAlpha := by
  let den := natToRat.comp (powTwoP.comp exponentP)
  refine (ratDiv.comp ((constant inputCode ratCode 1).pair den)).congrFun ?_
  intro x
  change 1 / ((2 ^ (precisionExponent x.2.length x.1 * (x.2.length+1)) : ℕ) : ℚ) = _
  simp [graphAlpha,searchDenominator,pow_mul]

noncomputable def graphScaleP : Procedure inputCode Nat.bits graphScale := by
  let dens := (listMap (0:ℚ) (0:ℕ) ratDen).comp (second Nat.bits vectorCode)
  exact binaryMul.comp ((ratDen.comp graphAlphaP).pair (natProductP.comp dens))

end Selector
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
