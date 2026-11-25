import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackTable
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

/-! Construct the complete residual Bellman graph by reading the serialized market,
current integral flow and terminal values. Both nested loops are bounded by list lengths. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Rows

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open GridMachine.Table

abbrev Stat := List Bool × (List Bool × List ℤ)
abbrev Dynamic := List ℕ × (List ℤ × List ℤ)
abbrev Raw := Stat × Dynamic
abbrev blist := listCode boolCode
abbrev ilist := listCode intCode
abbrev nlist := listCode Nat.bits
abbrev statCode := prodCode blist (prodCode blist ilist)
abbrev dynamicCode := prodCode nlist (prodCode ilist ilist)
abbrev rawCode := prodCode statCode dynamicCode

def read {α : Type*} (fallback : α) (xs : List α) (i : ℕ) : α := (xs.drop i).headD fallback

private noncomputable def statP := first statCode dynamicCode
private noncomputable def dynamicP := second statCode dynamicCode
private noncomputable def signsP := (first blist (prodCode blist ilist)).comp statP
private noncomputable def bidsPairP := (second blist (prodCode blist ilist)).comp statP
private noncomputable def eligibleP := (first blist ilist).comp bidsPairP
private noncomputable def bidsP := (second blist ilist).comp bidsPairP
private noncomputable def massP := (first nlist (prodCode ilist ilist)).comp dynamicP
private noncomputable def terminalsP := (second nlist (prodCode ilist ilist)).comp dynamicP
private noncomputable def expertTerminalP := (first ilist ilist).comp terminalsP
private noncomputable def optionTerminalP := (second ilist ilist).comp terminalsP

abbrev Request := (ℕ × ℕ) × Raw
abbrev requestCode := prodCode (prodCode Nat.bits Nat.bits) rawCode

/-- Emit a singleton for an actual residual arc, and the empty list when the option is
unavailable or a reverse arc has zero capacity. The target expert or option is a vertex
index while the last component identifies the modified amount. -/
def emit (forward : Bool) (z : Request) : List Arc :=
  let e := z.1.1
  let o := z.1.2
  let data := z.2
  let k := e * data.2.2.2.length + o
  let inc := !(xor forward (read false data.1.1 e))
  let valid := (read false data.1.2.1 k) && (inc || !decide (read 0 data.2.1 k = 0))
  let cost := read 0 data.1.2.2 k
  if valid then
    [((if forward then data.1.1.length + o else e, if inc then cost else -cost),
      if inc then 2*k else 2*k+1)]
  else []

/-- Literal binary-stack program for reading and testing one edge. -/
noncomputable def emitP (forward : Bool) : Procedure requestCode (listCode arcCode) (emit forward) := by
  let indices := first (prodCode Nat.bits Nat.bits) rawCode
  let raw := second (prodCode Nat.bits Nat.bits) rawCode
  let e := (first Nat.bits Nat.bits).comp indices
  let o := (second Nat.bits Nat.bits).comp indices
  let width := (listLength intCode 0).comp (optionTerminalP.comp raw)
  let m := (listLength boolCode false).comp (signsP.comp raw)
  let k := binaryAdd.comp ((binaryMul.comp (e.pair width)).pair o)
  let pos := (listGet boolCode false).comp (e.pair (signsP.comp raw))
  let allowed := (listGet boolCode false).comp (k.pair (eligibleP.comp raw))
  let flow := (listGet Nat.bits 0).comp (k.pair (massP.comp raw))
  let cost := (listGet intCode 0).comp (k.pair (bidsP.comp raw))
  let dir := constant requestCode boolCode forward
  let inc := boolNot.comp (boolXor.comp (dir.pair pos))
  let available := boolOr.comp (inc.pair (boolNot.comp (binaryZero.comp flow)))
  let valid := boolAnd.comp (allowed.pair available)
  let arg := identity requestCode
  let dest := ((choose e (binaryAdd.comp (m.pair o))).comp (dir.pair arg))
  let weight := (choose (intNeg.comp cost) cost).comp (inc.pair arg)
  let ident := (choose (doubleOne.comp k) (double.comp k)).comp (inc.pair arg)
  let entry := (dest.pair weight).pair ident
  let empty := constant requestCode (listCode arcCode) []
  let single := (listCons arcCode).comp (entry.pair empty)
  exact ((choose empty single).comp (valid.pair arg)).congrFun (fun _ => rfl)

abbrev rowArgCode := prodCode unaryCode rawCode

def edgeAt (forward : Bool) (z : ℕ × (ℕ × Raw)) : List Arc :=
  emit forward ((if forward then (z.2.1,z.1) else (z.1,z.2.1)),z.2.2)

private noncomputable def edgeAtP (forward : Bool) :
    Procedure (prodCode unaryCode rowArgCode) (listCode arcCode) (edgeAt forward) := by
  let other := unaryToBits.comp (first unaryCode rowArgCode)
  let ctx := second unaryCode rowArgCode
  let fromIdx := unaryToBits.comp ((first unaryCode rawCode).comp ctx)
  let raw := (second unaryCode rawCode).comp ctx
  cases forward
  · exact ((emitP false).comp ((other.pair fromIdx).pair raw)).congrFun (fun _ => rfl)
  · exact ((emitP true).comp ((fromIdx.pair other).pair raw)).congrFun (fun _ => rfl)

def row (forward : Bool) (z : ℕ × Raw) : Row :=
  let endValue := read 0 (if forward then z.2.2.2.1 else z.2.2.2.2) z.1
  let count := if forward then z.2.2.2.2.length else z.2.1.1.length
  (endValue, ((List.range count).map (fun j => edgeAt forward (j,z))).flatten)

noncomputable def rowP (forward : Bool) : Procedure rowArgCode rowCode (row forward) := by
  let raw := second unaryCode rawCode
  let index := unaryToBits.comp (first unaryCode rawCode)
  let getE := (listGet intCode 0).comp (index.pair (expertTerminalP.comp raw))
  let getO := (listGet intCode 0).comp (index.pair (optionTerminalP.comp raw))
  let countE := (Learning.GenerationCost.lengthUnaryP boolCode false).comp (signsP.comp raw)
  let countO := (Learning.GenerationCost.lengthUnaryP intCode 0).comp (optionTerminalP.comp raw)
  let tab := tabulate (f := fun ctx j => edgeAt forward (j,ctx)) [] (edgeAtP forward)
  let flat := Learning.GenerationCost.flattenP arcCode zeroArc
  cases forward
  · exact (getO.pair (flat.comp (tab.comp (countE.pair (identity rowArgCode))))).congrFun (fun _ => rfl)
  · exact (getE.pair (flat.comp (tab.comp (countO.pair (identity rowArgCode))))).congrFun (fun _ => rfl)

def make (x : Raw) : GridMachine.Table.Graph :=
  ((List.range x.1.1.length).map (fun i => row true (i,x))) ++
  ((List.range x.2.2.2.length).map (fun i => row false (i,x)))

/-- The whole residual graph, including dynamically loaded endpoint indices, signed costs,
capacity guards, arc identifiers, and rows for the dummy, is written by this program. -/
noncomputable def rowsP : Procedure rawCode graphCode make := by
  let countE := (Learning.GenerationCost.lengthUnaryP boolCode false).comp signsP
  let countO := (Learning.GenerationCost.lengthUnaryP intCode 0).comp optionTerminalP
  let experts := (tabulate (f := fun x i => row true (i,x)) zeroRow (rowP true)).comp (countE.pair (identity rawCode))
  let opts := (tabulate (f := fun x i => row false (i,x)) zeroRow (rowP false)).comp (countO.pair (identity rawCode))
  exact ((listAppend rowCode zeroRow).comp (experts.pair opts)).congrFun (fun _ => rfl)

theorem rows_deploy (o : OracleSpec.WordOracle) (x : Raw) :
    (OracleSpec.BitCode.deploy rowsP).ComputesWithin o (rawCode x)
      (3*rowsP.bound.eval (rawCode x).length + 2*(rawCode x).length + 2)
      (fun history bits => history = [] ∧ bits = graphCode (make x)) :=
  OracleSpec.BitCode.deploy_correct rowsP o x

end Rows
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
