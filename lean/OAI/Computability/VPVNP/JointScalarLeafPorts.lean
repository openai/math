import OAI.Computability.VPVNP.JointScalarMachine
import OAI.Computability.VPVNP.RankQueryStackSignedCount
import OAI.Computability.VPVNP.RankQueryGramReadSpace
import OAI.Computability.VPVNP.SliceArithmeticCallCopies

/-!
# Returning ports for an original Macaulay coefficient

The packed residual exponents and row register are immutable. The two
invocations of the counted checker share their input and advice, and write
their totals into the positive and negative operands of the field converter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open RAMTape UniversalCountStack

/-- Stack names for the row and exponent inputs, counter templates, row-prefix scratch, Boolean
checker and signed field conversion. -/
inductive Port where
  | row | packed | rowWidth | blankChoice | blankTotal | saved | staged
  | count (p : AdviceCountAdapter.Port)
  | arithmetic (p : SliceArithmeticSignedCount.Port)
  deriving DecidableEq, Fintype

/-- Checker input stack holding the polarity bit, equation address and packed exponent
coordinates. -/
abbrev queryPort : Port := .count (.aux .query)
/-- Counter stack holding the current Boolean witness for the advised circuit. -/
abbrev choicePort : Port := .count .choice
/-- Arithmetic input stack that receives the witness count for the selected polarity. A true
argument selects the negative count. -/
abbrev totalPort (neg : Bool) : Port := .arithmetic (.inr (SliceArithmeticSignedCount.source neg))
/-- Stack onto which the converter prepends the signed coefficient in the extension field’s
polynomial basis. -/
abbrev resultPort : Port := .arithmetic (.inr .result)
/-- Persistent checker stack containing the encoded gate instructions used for both witness
counts. -/
abbrev advicePort : Port := .count (.aux .advice)

/-- Static bank data, supplied once for the family of queries. The row width
is the expected width of the equation address in the circuit query. -/
structure Layout where
  /-- Prime modulus used to reduce the two integer witness counts. -/
  prime : ℕ
  /-- Number of base-field coordinates in the polynomial-basis encoding of a field element. -/
  degree : ℕ
  /-- Bit width of each base-field coordinate in the packed field result. -/
  limbWidth : ℕ
  /-- Number of row-address bits to place between the polarity bit and the exponent payload. -/
  rowBits : ℕ
  /-- Width of the enumerated witness word. Each count receives one extra bit to hold the total
  when every witness accepts. -/
  witnessBits : ℕ
  /-- Encoded Boolean gate instructions shared by the positive and negative coefficient
  queries. -/
  circuitAdvice : List Bool

/-- Initialize the leaf’s named stacks with the row, exponents, checker inputs, two count
operands and output suffix, using the layout for the advice and width templates. -/
def bank (L : Layout) (row packed query choice positive negative result : List Bool) : Stacks Port
  | .row => row
  | .packed => packed
  | .rowWidth => List.replicate L.rowBits false
  | .blankChoice => digits L.witnessBits 0
  | .blankTotal => digits (L.witnessBits+1) 0
  | .saved | .staged => []
  | .count p => UniversalCountStack.bank (AdviceCountAdapter.inputs query L.circuitAdvice) choice [] [] [] p
  | .arithmetic p => SliceArithmeticSignedCount.clean
      (SliceArithmeticSignedCount.external L.prime L.degree L.limbWidth positive negative result) p

/-- Leaf bank at a call boundary, with the row, packed exponents and output suffix in place and
the query, witness and count registers empty. -/
abbrev clean (L : Layout) (row packed result : List Bool) := bank L row packed [] [] [] [] result

/-- Route the checker’s total to the arithmetic operand for the selected polarity and its other
ports to the checker bank. -/
def countPorts (negative : Bool) : AdviceCountAdapter.Port → Port
  | .total => totalPort negative
  | p => .count p

private theorem countPorts_injective (negative : Bool) : Function.Injective (countPorts negative) := by
  intro i j h
  cases i <;> cases j <;> simp_all [countPorts, totalPort]

/-- Run the fixed circuit-witness enumerator with its total directed to the selected
signed-count operand. -/
def counter (neg : Bool) : FiniteRoutine Port := (FiniteRoutine.ofRoutine countCircuit).onPorts (countPorts neg)

/-- Reduce the two counts modulo the advised prime and prepend their difference as a constant
element of the extension field. -/
def reduce : FiniteRoutine Port := SliceArithmeticSignedCount.machine.onPorts Port.arithmetic

/-- Lift a counted checker call without charging its exponential elapsed time
to the space bound. The unselected count operand remains available. -/
theorem counter_bounded (neg : Bool) (L : Layout) (row packed query choice other input output suffix : List Bool)
    {cap t : ℕ}
    (small : SpaceRun countCircuit.standalone cap t (some countCircuit.entry)
      (UniversalCountStack.bank (AdviceCountAdapter.inputs query L.circuitAdvice) choice input [] []) none
      (UniversalCountStack.bank (AdviceCountAdapter.inputs query L.circuitAdvice) choice output [] []))
    (hin : ∀ p, (bank L row packed query choice (if neg then other else input)
      (if neg then input else other) suffix p).length ≤ cap) :
    (counter neg).BoundedRun cap t
      (bank L row packed query choice (if neg then other else input) (if neg then input else other) suffix)
      (bank L row packed query choice (if neg then other else output) (if neg then output else other) suffix) := by
  apply FiniteRoutine.BoundedRun.framed (countPorts_injective neg) (r := FiniteRoutine.ofRoutine countCircuit)
    small hin
  · intro i
    cases i <;> cases neg <;> rfl
  · intro i
    cases i <;> cases neg <;> rfl
  · intro i h
    cases i with
    | arithmetic a =>
      rcases a with a|a
      · cases a with
        | divide i => cases i <;> rfl
        | _ => rfl
      · cases a <;> cases neg <;> first | rfl | exact (h .total rfl).elim
    | _ => rfl

/-- The converter reads both totals in place and writes only the field-result
port. The larger stack bank keeps the row, packed input and checker advice. -/
theorem reduce_bounded {p e v : ℕ} [Fact p.Prime] [NeZero e] (c : SliceArithmetic.Vector p e)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (L : Layout) (hp : L.prime = p)
    (he : L.degree = e) (hwidth : L.limbWidth = v) (z : ℤ)
    (row packed query choice positive negative result : List Bool)
    (hsign : (TapeWord.value positive : ℤ) - (TapeWord.value negative : ℤ) = z) (cap : ℕ)
    (hcap : positive.length+negative.length+result.length+e+v+
      SliceArithmeticSignedCount.callCap positive.length negative.length e v ≤ cap)
    (hin : ∀ a, (bank L row packed query choice positive negative result a).length ≤ cap) :
    ∃ ticks ≤ SliceArithmeticSignedCount.callCap positive.length negative.length e v,
      reduce.BoundedRun cap ticks (bank L row packed query choice positive negative result)
        (bank L row packed query choice positive negative (RankQuery.Stack.Engine.scalar v (z : RankQuery.Stack.Scalar c) ++ result)) := by
  obtain ⟨ticks,ht,hr⟩ := RankQuery.Stack.Scalar.signedCount_spaceRun hv c z positive negative result hsign
  refine ⟨ticks,ht,?_⟩
  apply FiniteRoutine.BoundedRun.framed (fun _ _ h => Port.arithmetic.inj h)
    (r := SliceArithmeticSignedCount.machine) (hr.mono_cap hcap) hin
  · intro a
    simp only [bank, hp, he, hwidth]
  · intro a
    simp only [bank, hp, he, hwidth]
  · intro a h
    cases a <;> first | rfl | exact (h _ rfl).elim

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
