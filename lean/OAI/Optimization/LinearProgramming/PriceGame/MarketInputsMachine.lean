import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Computability.QuantumFactoring.BitStackListFold
import OAI.Optimization.LinearProgramming.PriceGame.MarketDenominator

/-! # Binary-stack procedures for clearing the market's denominators -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace InputMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- The same scaled natural supply as the flow solver, on the input word
containing the prescribed denominator and the original rational weight. -/
noncomputable def qtyP : Procedure (prodCode Nat.bits ratCode) Nat.bits
    (fun p => Denominator.qty p.1 p.2) := by
  let Q := first Nat.bits ratCode
  let weight := second Nat.bits ratCode
  let mag := intAbs.comp (ratNum.comp weight)
  let scale := binaryDiv.comp (Q.pair (ratDen.comp weight))
  exact binaryMul.comp (mag.pair scale)

private theorem den_bits_le (w : ℚ) : w.den.bits.length ≤ (ratCode w).length := by
  simp only [ratCode, prodCode, pairBits_length]
  omega

private theorem product_bits (xs : List ℚ) (n : ℕ) :
    (xs.foldl (fun t x => t * x.den) n).bits.length ≤ n.bits.length + (listCode ratCode xs).length := by
  induction xs generalizing n with
  | nil => simp [listCode]
  | cons x xs ih =>
    have hMul := bits_length_mul n x.den
    have hDen := den_bits_le x
    have hRest := ih (n * x.den)
    rw [List.foldl_cons, listCode_length_cons]
    omega

/-- A full polynomial-time bit program for the product of weight denominators.
Every intermediate product is bounded in length by the actual framed input. -/
noncomputable def denominatorP : Procedure (listCode ratCode) Nat.bits
    (fun ws => ws.foldl (fun p x => p * x.den) 1) := by
  let step : Procedure (prodCode ratCode Nat.bits) Nat.bits (fun x => x.2 * x.1.den) :=
    binaryMul.comp ((second ratCode Nat.bits).pair (ratDen.comp (first ratCode Nat.bits)))
  let fold := foldList (0 : ℚ) step Polynomial.X (by
    intro xs b i
    rw [Polynomial.eval_X]
    change ((xs.take i).foldl (fun t x => t * x.den) b).bits.length ≤ _
    have hh := product_bits (xs.take i) b
    have hl := listCode_length_take_le ratCode i xs
    omega)
  exact fold.comp ((identity (listCode ratCode)).pair (constant (listCode ratCode) Nat.bits 1))

theorem denominatorP_agrees {m : ℕ} (L : Fin m → ℚ) :
    ((List.finRange m).map L).foldl (fun p x => p * x.den) 1 = Denominator.denominator L := by
  have h (xs : List ℚ) (a : ℕ) :
      xs.foldl (fun p x => p*x.den) a = a * (xs.map Rat.den).prod := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih => simp [ih, mul_assoc]
  rw [h, one_mul, List.map_map]
  change ((List.finRange m).map (fun e => (L e).den)).prod = ∏ e, (L e).den
  rw [← List.ofFn_eq_map]
  exact List.prod_ofFn

end InputMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
