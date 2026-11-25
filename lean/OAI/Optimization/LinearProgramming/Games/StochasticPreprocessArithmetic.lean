import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap
import OAI.Optimization.LinearProgramming.Games.ChancePrecision
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

/-! Binary products and the small-discount parameters. The exponent and factorial
argument are both supplied in unary. Each intermediate binary product fits in
the combined length of the factors that have actually been read. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace Stochastic
namespace Preprocess

open OracleSpec ExactQuantumFactoring.BitStackProgram Procedure

private theorem productFold (xs : List ℕ) (b : ℕ) :
    xs.foldl (fun acc x => acc*x) b = b*xs.prod := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_assoc]

private theorem productFold_width (xs : List ℕ) (b : ℕ) :
    (xs.foldl (fun acc x => acc*x) b).bits.length ≤ b.bits.length + (listCode Nat.bits xs).length := by
  induction xs generalizing b with
  | nil => simp [listCode]
  | cons x xs ih =>
    have h := bits_length_mul b x
    have ht := ih (b*x)
    rw [List.foldl_cons,listCode_length_cons]
    omega

noncomputable def productP : Procedure (listCode Nat.bits) Nat.bits List.prod := by
  let step : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun t => t.2*t.1) :=
    binaryMul.comp (swap Nat.bits Nat.bits)
  let loop := foldList 0 step Polynomial.X (by
    intro xs b i
    rw [Polynomial.eval_X]
    have h := productFold_width (xs.take i) b
    have ht := listCode_length_take_le Nat.bits i xs
    change ((xs.take i).foldl (fun a x => a*x) b).bits.length ≤ _
    omega)
  apply (loop.comp ((identity (listCode Nat.bits)).pair (constant _ Nat.bits 1))).congrFun
  intro xs
  change xs.foldl (fun a x => a*x) 1 = _
  simp [productFold]

private theorem factorial_range (n : ℕ) : ((List.range n).map Nat.succ).prod = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ,ih,Nat.factorial_succ,Nat.mul_comm]

/-- Compute the factorial by writing the successive factors in binary and multiplying. -/
noncomputable def factorialP : Procedure unaryCode Nat.bits Nat.factorial := by
  let vals := (listMap 0 0 successor).comp PriceGame.Control.Native.addressRangeP
  apply (productP.comp vals).congrFun
  exact factorial_range

private theorem constant_range_prod (b n : ℕ) : ((List.range n).map fun _ => b).prod = b^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ,pow_succ]

/-- A binary base with an input-supported unary exponent. -/
noncomputable def powerP : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun t => t.2^t.1) := by
  let row := tabulate (f := fun (b : ℕ) (_ : ℕ) => b) 0 (second unaryCode Nat.bits)
  exact (productP.comp row).congrFun (fun t => constant_range_prod t.2 t.1)

abbrev paramCode := prodCode unaryCode (prodCode Nat.bits Nat.bits)
abbrev pairNat := prodCode Nat.bits Nat.bits

/-- Construct the Cramer denominator bound from vertex count, Q and W. -/
noncomputable def cramerP : Procedure paramCode Nat.bits
    (fun x => denominatorBound x.1 x.2.1 x.2.2) := by
  let n := first unaryCode pairNat
  let qw := second unaryCode pairNat
  let q := (first Nat.bits Nat.bits).comp qw
  let w := (second Nat.bits Nat.bits).comp qw
  let threeW := binaryAdd.comp ((constant paramCode Nat.bits 3).pair w)
  let base := binaryMul.comp (q.pair threeW)
  exact binaryMul.comp ((factorialP.comp n).pair (powerP.comp (n.pair base)))

noncomputable def slopeP : Procedure pairNat Nat.bits (fun t => slopeBound t.1 t.2) := by
  let a := first Nat.bits Nat.bits
  let w := second Nat.bits Nat.bits
  exact binaryMul.comp ((binaryAdd.comp (w.pair (constant pairNat Nat.bits 4))).pair a)

noncomputable def naturalRatP : Procedure Nat.bits ratCode (fun n : ℕ => (n : ℚ)) :=
  (intToRat.comp natToInt).congrFun (by intro n; simp)

noncomputable def discountP : Procedure pairNat ratCode (fun t => chanceDiscount t.1 t.2) := by
  let a := naturalRatP.comp (first Nat.bits Nat.bits)
  let h := naturalRatP.comp (second Nat.bits Nat.bits)
  let aa := ratMul.comp (a.pair a)
  let den := ratMul.comp ((ratMul.comp ((constant pairNat ratCode 32).pair h)).pair aa)
  apply (ratDiv.comp ((constant pairNat ratCode 1).pair den)).congrFun
  intro t
  simp [chanceDiscount,pow_two]

noncomputable def accuracyP : Procedure Nat.bits ratCode chancePrecision := by
  let aa := ratMul.comp (naturalRatP.pair naturalRatP)
  let den := ratMul.comp ((constant Nat.bits ratCode 16).pair aa)
  apply (ratDiv.comp ((constant Nat.bits ratCode 1).pair den)).congrFun
  intro t
  simp [chancePrecision,pow_two]

/-- Scale the requested accuracy from the reward interval to the unit box. -/
noncomputable def normalizedAccuracyP : Procedure pairNat ratCode
    (fun x => chancePrecision x.1 / (2*(x.2 : ℚ))) := by
  let w := naturalRatP.comp (second Nat.bits Nat.bits)
  let den := ratMul.comp ((constant pairNat ratCode 2).pair w)
  exact ratDiv.comp ((accuracyP.comp (first Nat.bits Nat.bits)).pair den)

end Preprocess
end Stochastic
end Games
end LinearProgramming
end Optimization
end OAI
