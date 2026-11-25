import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackInput
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineRows
import OAI.Optimization.LinearProgramming.PriceGame.MarketLCMMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! # Initial transshipment word of a rational market

The supply unit is supplied by the caller, whereas the signed cost grid is
computed from the actual bids. Dummy entries of the dense table occur at the
start of each expert row. Every tabulation is bounded by a length in the input.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace InitializeMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open GridMachine

/-- (supply unit, weights), (number of options, (signs, availability, bids)). -/
abbrev RationalStatic := List Bool × (List Bool × List ℚ)
abbrev Input := (ℕ × List ℚ) × (ℕ × RationalStatic)
abbrev blist := listCode boolCode
abbrev qlist := listCode ratCode
abbrev zlist := listCode intCode
abbrev nlist := listCode Nat.bits
abbrev rationalStaticCode := prodCode blist (prodCode blist qlist)
abbrev inputCode : Input → List Bool := prodCode (prodCode Nat.bits qlist) (prodCode unaryCode rationalStaticCode)
abbrev environmentCode := prodCode (prodCode intCode FlowMachine.Rows.statCode) FlowMachine.Rows.dynamicCode
abbrev outputCode := prodCode nlist environmentCode

private theorem foldMax_member (xs : List ℚ) (a : ℚ) :
    xs.foldl (fun best q => max q best) a = a ∨ xs.foldl (fun best q => max q best) a ∈ xs := by
  induction xs generalizing a with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    rcases ih (max x a) with h | h
    · by_cases hx : x ≤ a
      · exact Or.inl (h.trans (max_eq_right hx))
      · exact Or.inr (List.mem_cons.mpr (Or.inl (h.trans (max_eq_left (le_of_not_ge hx)))))
    · exact Or.inr (List.mem_cons_of_mem _ h)

noncomputable def maxP : Procedure qlist ratCode
    (fun xs => xs.foldl (fun best q => max q best) 0) := by
  let fold := foldList (0:ℚ) Control.Native.ratMaxP Polynomial.X (by
    intro xs a i
    rw [Polynomial.eval_X]
    change (ratCode ((xs.take i).foldl (fun best q => max q best) a)).length ≤ _
    rcases foldMax_member (xs.take i) a with h | h
    · rw [h]; omega
    · have hl := code_le_of_mem ratCode (List.mem_of_mem_take h)
      omega)
  exact fold.comp ((identity qlist).pair (constant qlist ratCode 0))

noncomputable def absoluteP : Procedure ratCode ratCode (fun x : ℚ => |x|) :=
  (Control.Native.ratMaxP.comp ((identity ratCode).pair ratNeg)).congrFun
    (fun _ => abs_eq_max_neg.symm)

def maxAbsolute (xs : List ℚ) : ℚ := (xs.map (fun x => |x|)).foldl (fun best q => max q best) 0
noncomputable def maxAbsoluteP : Procedure qlist ratCode maxAbsolute :=
  maxP.comp (listMap (0:ℚ) (0:ℚ) absoluteP)

def grid (xs : List ℚ) : ℕ := xs.foldl (fun n q => n*q.den) 1

def initialWord (x : Input) : List ℕ ×
    ((ℤ × FlowMachine.Rows.Stat) × FlowMachine.Rows.Dynamic) :=
  let Q := x.1.1
  let ws := x.1.2
  let g := x.2.1
  let raw := x.2.2
  let bids := raw.2.2
  let D := grid bids
  let M := Grid.scaleInput D (maxAbsolute bids)
  let fixed := ((D:ℤ),raw.1,raw.2.1,bids.map (Grid.scaleInput D))
  let flow := bids.map (fun _ => 0)
  let experts := raw.1.map fun positive => if positive then M else -M
  let options := (List.range g).map fun _ => (0:ℤ)
  (ws.map (Denominator.qty Q), fixed, flow, experts, options)

private noncomputable def signedP : Procedure (prodCode intCode boolCode) intCode
    (fun z => if z.2 then z.1 else -z.1) := by
  let x := first intCode boolCode
  exact (conditional (second intCode boolCode) x (intNeg.comp x)).congrFun (fun _ => rfl)

/-- Single fixed bit program computing the signed initial state and every scaled capacity. -/
noncomputable def initializeP : Procedure inputCode outputCode initialWord := by
  let amt := first (prodCode Nat.bits qlist) (prodCode unaryCode rationalStaticCode)
  let other := second (prodCode Nat.bits qlist) (prodCode unaryCode rationalStaticCode)
  let Q := (first Nat.bits qlist).comp amt
  let weights := (second Nat.bits qlist).comp amt
  let g := (first unaryCode rationalStaticCode).comp other
  let raw := (second unaryCode rationalStaticCode).comp other
  let signs := (first blist (prodCode blist qlist)).comp raw
  let right := (second blist (prodCode blist qlist)).comp raw
  let available := (first blist qlist).comp right
  let bids := (second blist qlist).comp right
  let D := InputMachine.denominatorP.comp bids
  let scaled := (mapWithContext (0:ℚ) (0:ℤ) Table.Input.scaleProgram).comp (bids.pair D)
  let M := Table.Input.scaleProgram.comp (D.pair (maxAbsoluteP.comp bids))
  let quantities := (mapWithContext (0:ℚ) 0 InputMachine.qtyP).comp (weights.pair Q)
  let fixed := (natToInt.comp D).pair (signs.pair (available.pair scaled))
  let flow := (listMap (0:ℚ) 0 (constant ratCode Nat.bits 0)).comp bids
  let experts := (mapWithContext false (0:ℤ) signedP).comp (signs.pair M)
  let opts := (listMap 0 (0:ℤ) (constant Nat.bits intCode (0:ℤ))).comp (Control.Native.addressRangeP.comp g)
  exact (quantities.pair (fixed.pair (flow.pair (experts.pair opts)))).congrFun (fun _ => rfl)

/-- In a recursive trial the supplied unit is itself computed from the weight vector. -/
noncomputable def initialLCMP : Procedure
    (prodCode qlist (prodCode unaryCode rationalStaticCode)) outputCode
    (fun x => initialWord ((x.1.foldl (fun n q => Nat.lcm n q.den) 1,x.1),x.2)) := by
  let ws := first qlist (prodCode unaryCode rationalStaticCode)
  let raw := second qlist (prodCode unaryCode rationalStaticCode)
  exact initializeP.comp (((InputMachine.leastDenominatorP.comp ws).pair ws).pair raw)

end InitializeMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
