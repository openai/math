import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Computability.QuantumFactoring.BitStackListOps
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingBounds
import OAI.Optimization.LinearProgramming.PriceGame.MarketDenominator
import OAI.Optimization.LinearProgramming.PriceGame.MomentRational

/-! # Compiled rational and binary weight folds for a trial preparation -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- In a product of reduced rationals both numerator and denominator grow by
at most the sum of the respective input bit lengths. -/
theorem rat_product_length (x y : ℚ) :
    (ratCode (x*y)).length ≤ (ratCode x).length + (ratCode y).length := by
  have hn : (x*y).num.natAbs ≤ x.num.natAbs * y.num.natAbs := by
    rw [Rat.mul_num]
    simpa only [Int.natAbs_mul] using Int.natAbs_ediv_le_natAbs (x.num * y.num) _
  have hd : (x*y).den ≤ x.den * y.den :=
    Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.mul_den_dvd _ _)
  have nsize := (Nat.size_le_size hn).trans (Market.Denominator.size_mul_le_add _ _)
  have dsize := (Nat.size_le_size hd).trans (Market.Denominator.size_mul_le_add _ _)
  simp only [Wire.rat_length]
  omega

private theorem rat_fold_length (xs : List ℚ) (b : ℚ) :
    (ratCode (xs.foldl (fun p x => x*p) b)).length ≤ (ratCode b).length + (listCode ratCode xs).length := by
  induction xs generalizing b with
  | nil => simp [listCode]
  | cons x xs ih =>
    have h := ih (x*b)
    have hm := rat_product_length x b
    rw [List.foldl_cons, listCode_length_cons]
    omega

private theorem rat_fold_mul (xs : List ℚ) (b : ℚ) : xs.foldl (fun p x => x*p) b = b * xs.prod := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih, List.prod_cons]
    ring

noncomputable def productWeightsP : Procedure (prodCode (listCode ratCode) ratCode) ratCode
    (fun x => x.2 * x.1.prod) := by
  let fold := foldList (0 : ℚ) ratMul Polynomial.X (by
    intro xs b i
    change (ratCode ((xs.take i).foldl (fun p x => x*p) b)).length ≤ _
    have h := rat_fold_length (xs.take i) b
    have h' := listCode_length_take_le ratCode i xs
    rw [Polynomial.eval_X]; omega)
  exact fold.congrFun (by intro p; exact rat_fold_mul _ _)

/-- Fixed learning-rate multiplication and addition in ordinary signed rational encoding. -/
noncomputable def gainMultiplierP : Procedure ratCode ratCode (fun z => 1 + Moment.etaQ * z) :=
  ratAdd.comp ((constant ratCode ratCode 1).pair
    (ratMul.comp ((constant ratCode ratCode Moment.etaQ).pair (identity ratCode))))

noncomputable def gainProductP : Procedure (prodCode (listCode ratCode) ratCode) ratCode
    (fun x => x.2 * (x.1.map (fun g => 1 + Moment.etaQ*g)).prod) :=
  productWeightsP.comp (((listMap 0 0 gainMultiplierP).comp (first (listCode ratCode) ratCode)).pair
    (second (listCode ratCode) ratCode))

private theorem sum_fold_len (xs : List ℕ) (b : ℕ) :
    (xs.foldl (fun p x => x+p) b).bits.length ≤ b.bits.length + (listCode Nat.bits xs).length := by
  induction xs generalizing b with
  | nil => simp [listCode]
  | cons x xs ih =>
    have hs := ih (x+b)
    have hb := bits_length_add x b
    rw [List.foldl_cons, listCode_length_cons]
    omega

noncomputable def sumWeightScoresP : Procedure (listCode Nat.bits) Nat.bits List.sum := by
  let fold := foldList 0 binaryAdd Polynomial.X (by
    intro xs b i
    change ((xs.take i).foldl (fun p x => x+p) b).bits.length ≤ _
    have h := sum_fold_len (xs.take i) b
    have ht := listCode_length_take_le Nat.bits i xs
    rw [Polynomial.eval_X]
    omega)
  have hs (xs : List ℕ) (b : ℕ) : xs.foldl (fun p x => x+p) b = xs.sum + b := by
    induction xs generalizing b with
    | nil => simp
    | cons x xs ih => simp [ih]; omega
  exact (fold.comp ((identity (listCode Nat.bits)).pair (constant (listCode Nat.bits) Nat.bits 0))).congrFun
    (by intro xs; simpa only [Function.comp_apply, id_eq, Nat.add_zero] using hs xs 0)

/-- Bounded power construction. The fuel is measured in unary. The counter
is a binary score. A zero counter leaves both registers in place. -/
def exponentTick (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.1 = 0 then x else (x.1-1,2*x.2)

private noncomputable def exponentTickP : Procedure (prodCode Nat.bits Nat.bits)
    (prodCode Nat.bits Nat.bits) exponentTick := by
  let ec := prodCode Nat.bits Nat.bits
  let n := first Nat.bits Nat.bits
  let acc := second Nat.bits Nat.bits
  let dec := binarySub.comp (n.pair (constant ec Nat.bits 1))
  let upd := dec.pair (double.comp acc)
  exact (conditional (binaryZero.comp n) (identity ec) upd).congrFun
    (by intro x; simp [exponentTick])

theorem exponentTick_iter (k n a : ℕ) :
    (exponentTick^[k]) (n,a) = (n-k, 2^(min k n)*a) := by
  induction k generalizing n a with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases n with
    | zero => simpa [exponentTick] using ih 0 a
    | succ n =>
      have hm : min (k+1) (n+1) = min k n + 1 := by omega
      simp only [exponentTick, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one, ih,
        hm, pow_succ]
      congr 1 <;> first | omega | ring

private theorem iter_exponent_width (k n a : ℕ) :
    (prodCode Nat.bits Nat.bits ((exponentTick^[k]) (n,a))).length ≤
      (prodCode Nat.bits Nat.bits (n,a)).length + k + 1 := by
  rw [exponentTick_iter]
  have hlow : (n-k).bits.length ≤ n.bits.length := by
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (Nat.sub_le n k)
  have hmul := bits_length_mul (2^(min k n)) a
  have hpow : (2^(min k n)).bits.length = min k n + 1 := by simp [Nat.size_eq_bits_len, Nat.size_pow]
  simp only [prodCode, pairBits_length]
  omega

/-- A genuine polynomial-time binary-stack program even on arbitrary inputs.
On a valid trace its unary fuel dominates the score and the power is exact. -/
noncomputable def boundedPowerTwoP : Procedure (prodCode unaryCode Nat.bits) Nat.bits
    (fun x => 2 ^ min x.1 x.2) := by
  let st := prodCode Nat.bits Nat.bits
  let loop := exponentTickP.iterate (Polynomial.X+1) (by
    rintro k ⟨n,a⟩ i hi
    have hh := iter_exponent_width i n a
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega)
  let clock := first unaryCode Nat.bits
  let n := second unaryCode Nat.bits
  let one := constant (prodCode unaryCode Nat.bits) Nat.bits 1
  exact ((second Nat.bits Nat.bits).comp (loop.comp (clock.pair (n.pair one)))).congrFun
    (by rintro ⟨k,n⟩; change ((exponentTick^[k]) (n,1)).2 = _; simp [exponentTick_iter])

/-- Multiply the incoming rational exactly by the power indicated by the
score sum up to the supplied unary cap. -/
noncomputable def scoreProductP : Procedure (prodCode unaryCode (prodCode (listCode Nat.bits) ratCode))
    ratCode (fun x => x.2.2 * (2 : ℚ) ^ min x.1 x.2.1.sum) := by
  let clock := first unaryCode (prodCode (listCode Nat.bits) ratCode)
  let rest := second unaryCode (prodCode (listCode Nat.bits) ratCode)
  let scores := (first (listCode Nat.bits) ratCode).comp rest
  let weight := (second (listCode Nat.bits) ratCode).comp rest
  let p := natToRat.comp (boundedPowerTwoP.comp (clock.pair (sumWeightScoresP.comp scores)))
  exact (ratMul.comp (weight.pair p)).congrFun (by
    intro x
    change x.2.2 * ((2 ^ min x.1 x.2.1.sum : ℕ) : ℚ) = _
    simp)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
