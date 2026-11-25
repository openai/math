import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineRows
import OAI.Optimization.LinearProgramming.PriceGame.MarketOutputsMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! A finite bit-stack program produces the allocation at every option of every expert,
including the dummy and experts whose original quantity was zero. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open OutputMachine

abbrev Prices := List ℚ
abbrev pricesCode := listCode ratCode
/-- Quantities, common denominator, static market, current dense flow, real-good prices. -/
abbrev Frame := (List ℕ × ℕ) × (Rows.Stat × (Flow × Prices))
abbrev frameCode := prodCode (prodCode flowCode Nat.bits) (prodCode Rows.statCode (prodCode flowCode pricesCode))
abbrev Request := (ℕ × ℕ) × Frame
abbrev requestCode := prodCode (prodCode Nat.bits Nat.bits) frameCode
abbrev rowCode := prodCode unaryCode frameCode
abbrev Expert := ℕ × Frame
abbrev expertCode := prodCode Nat.bits frameCode

private noncomputable abbrev qdP := first (prodCode flowCode Nat.bits) (prodCode Rows.statCode (prodCode flowCode pricesCode))
private noncomputable abbrev restP := second (prodCode flowCode Nat.bits) (prodCode Rows.statCode (prodCode flowCode pricesCode))
private noncomputable abbrev qtyP := (first flowCode Nat.bits).comp qdP
private noncomputable abbrev denomP := (second flowCode Nat.bits).comp qdP
private noncomputable abbrev statP := (first Rows.statCode (prodCode flowCode pricesCode)).comp restP
private noncomputable abbrev fpP := (second Rows.statCode (prodCode flowCode pricesCode)).comp restP
private noncomputable abbrev flowP := (first flowCode pricesCode).comp fpP
private noncomputable abbrev pricesP := (second flowCode pricesCode).comp fpP
private noncomputable abbrev signsP := (first Rows.blist (prodCode Rows.blist Rows.ilist)).comp statP
private noncomputable abbrev fieldsP := (second Rows.blist (prodCode Rows.blist Rows.ilist)).comp statP
private noncomputable abbrev flagsP := (first Rows.blist Rows.ilist).comp fieldsP
private noncomputable abbrev costsP := (second Rows.blist Rows.ilist).comp fieldsP
private noncomputable abbrev indsP := first (prodCode Nat.bits Nat.bits) frameCode
private noncomputable abbrev frameP := second (prodCode Nat.bits Nat.bits) frameCode
private noncomputable abbrev expertP := (first Nat.bits Nat.bits).comp indsP
private noncomputable abbrev indexP := (second Nat.bits Nat.bits).comp indsP
private noncomputable abbrev priceLenP := (listLength ratCode 0).comp pricesP
private noncomputable abbrev widthP := binaryAdd.comp ((priceLenP.comp frameP).pair (constant requestCode Nat.bits 1))
private noncomputable abbrev firstCellP := binaryMul.comp (expertP.pair widthP)

def candidate (x : Request) : List ScoredOption :=
  let e := x.1.1
  let j := x.1.2
  let t := x.2
  let k := e*(t.2.2.2.length+1)+(j+1)
  let bid := mkRat (Rows.read 0 t.2.1.2.2 k) t.1.2
  let y := Rows.read 0 t.2.2.2 j
  if Rows.read false t.2.1.2.1 k then
    [(j+1,if Rows.read false t.2.1.1 e then bid - y else bid + y)]
  else []

noncomputable def candidateP : Procedure requestCode (listCode scoredCode) candidate := by
  let number := binaryAdd.comp (indexP.pair (constant requestCode Nat.bits 1))
  let idx := binaryAdd.comp (firstCellP.pair number)
  let sign := (listGet boolCode false).comp (expertP.pair (signsP.comp frameP))
  let enabled := (listGet boolCode false).comp (idx.pair (flagsP.comp frameP))
  let cost := (listGet intCode 0).comp (idx.pair (costsP.comp frameP))
  let bid := makeRat.comp (cost.pair (denomP.comp frameP))
  let price := (listGet ratCode 0).comp (indexP.pair (pricesP.comp frameP))
  let utility := quoteP.comp (sign.pair (bid.pair price))
  let nilP := constant requestCode (listCode scoredCode) []
  let singleton := (listCons scoredCode).comp ((number.pair utility).pair nilP)
  exact ((choose nilP singleton).comp (enabled.pair (identity requestCode))).congrFun (fun _ => rfl)

/-- Ties preserve the earlier available good. The outside option, always eligible,
is the original incumbent. -/
def chosen (x : Expert) : ℕ :=
  ((((List.range x.2.2.2.2.length).map (fun j => candidate ((x.1,j),x.2))).flatten).foldl
    (fun b a => chooseBetter (a,b)) (0,0)).1

noncomputable def chosenP : Procedure expertCode Nat.bits chosen := by
  let row := second unaryCode expertCode
  let e := (first Nat.bits frameCode).comp row
  let t := (second Nat.bits frameCode).comp row
  let j := unaryToBits.comp (first unaryCode expertCode)
  let item := candidateP.comp ((e.pair j).pair t)
  let all := tabulate (f := fun (x : Expert) j => candidate ((x.1,j),x.2)) [] item
  let count := (Learning.GenerationCost.lengthUnaryP ratCode 0).comp (pricesP.comp (second Nat.bits frameCode))
  let options := (Learning.GenerationCost.flattenP scoredCode (0,0)).comp
    (all.comp (count.pair (identity expertCode)))
  let best := bestRowP.comp (options.pair (constant expertCode scoredCode (0,0)))
  exact ((first Nat.bits ratCode).comp best).congrFun (fun _ => rfl)

def amount (x : Request) : ℚ :=
  let e := x.1.1
  let j := x.1.2
  let t := x.2
  let q := Rows.read 0 t.1.1 e
  let k := e*(t.2.2.2.length+1)+j
  if q=0 then (if j = chosen (e,t) then 1 else 0)
  else ((Rows.read 0 t.2.2.1 k : ℕ) : ℚ) / (q : ℚ)

noncomputable def amountP : Procedure requestCode ratCode amount := by
  let qty := (listGet Nat.bits 0).comp (expertP.pair (qtyP.comp frameP))
  let zero := binaryZero.comp qty
  let k := binaryAdd.comp (firstCellP.pair indexP)
  let flowing := (listGet Nat.bits 0).comp (k.pair (flowP.comp frameP))
  let frac := fractionP.comp (flowing.pair qty)
  let best := chosenP.comp (expertP.pair frameP)
  let win := Control.Native.natEqP.comp (indexP.pair best)
  let point := (choose (constant requestCode ratCode 0) (constant requestCode ratCode 1)).comp
    (win.pair (identity requestCode))
  exact ((choose frac point).comp (zero.pair (identity requestCode))).congrFun (by
    intro x
    simp [amount, Function.comp_def, Rows.read])

def allocationsRow (x : ℕ × Frame) : List ℚ :=
  (List.range (x.2.2.2.2.length+1)).map fun j => amount ((x.1,j),x.2)

noncomputable def allocationsRowP : Procedure rowCode pricesCode allocationsRow := by
  let row := second unaryCode rowCode
  let e := unaryToBits.comp ((first unaryCode frameCode).comp row)
  let t := (second unaryCode frameCode).comp row
  let j := unaryToBits.comp (first unaryCode rowCode)
  let item := amountP.comp ((e.pair j).pair t)
  let tab := tabulate (f := fun (x : ℕ × Frame) j => amount ((x.1,j),x.2)) (0:ℚ) item
  let count := unarySuccessor.comp ((Learning.GenerationCost.lengthUnaryP ratCode 0).comp
    (pricesP.comp (second unaryCode frameCode)))
  exact (tab.comp (count.pair (identity rowCode))).congrFun (fun _ => rfl)

def allocations (x : Frame) : List ℚ :=
  ((List.range x.2.1.1.length).map fun e => allocationsRow (e,x)).flatten

noncomputable def allocationsP : Procedure frameCode pricesCode allocations := by
  let count := (Learning.GenerationCost.lengthUnaryP boolCode false).comp signsP
  let rows := (tabulate (f := fun x e => allocationsRow (e,x)) [] allocationsRowP).comp
    (count.pair (identity frameCode))
  exact ((Learning.GenerationCost.flattenP ratCode 0).comp rows).congrFun (fun _ => rfl)

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
