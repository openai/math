import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineTerminal
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineRows

/-! One complete serialized expert update: write residual rows, run Bellman, update flows,
and copy the newly computed potential words. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open GridMachine.Table

abbrev Fixed := ℤ × FlowMachine.Rows.Stat
abbrev Dynamic := FlowMachine.Rows.Dynamic
abbrev Environment := Fixed × Dynamic
abbrev fixedCode : Fixed → List Bool := prodCode intCode FlowMachine.Rows.statCode
abbrev dynCode : Dynamic → List Bool := FlowMachine.Rows.dynamicCode
abbrev envCode : Environment → List Bool := prodCode fixedCode dynCode
abbrev unitCode := prodCode Nat.bits envCode

/-- A block length is supplied in unary; its offset is binary and is never used as a clock. -/
abbrev Block := ℕ × (ℕ × List Item)
abbrev blockCode : Block → List Bool := prodCode unaryCode (prodCode Nat.bits valuesCode)

def block (x : Block) : Bank :=
  (List.range x.1).map fun j => ((x.2.2.drop (x.2.1+j)).headD zeroItem).1.1

noncomputable def blockP : Procedure blockCode bankCode block := by
  let env := prodCode Nat.bits valuesCode
  let k := unaryToBits.comp (first unaryCode env)
  let args := second unaryCode env
  let offset := (first Nat.bits valuesCode).comp args
  let vals := (second Nat.bits valuesCode).comp args
  let j := binaryAdd.comp (offset.pair k)
  let entry := (listGet itemCode zeroItem).comp (j.pair vals)
  let score := (first intCode intCode).comp ((first GridMachine.keyCode routeCode).comp entry)
  exact (tabulate (f := fun x k => ((x.2.drop (x.1+k)).headD zeroItem).1.1) (0:ℤ) score).congrFun
    (fun _ => rfl)

abbrev Finish := Seed × (FlowMachine.Flow × List Item)
abbrev finishCode : Finish → List Bool := prodCode seedCode (prodCode FlowMachine.flowCode valuesCode)

def finishStep (x : Finish) : Dynamic :=
  let s := x.1
  let vals := x.2.2
  let path := ((vals.drop (sourceIndex s)).headD zeroItem).2
  (FlowMachine.update (x.2.1,path), (block (s.2.2.2.1.length,(0,vals)),
    block (s.2.2.2.2.length,(s.2.1.length,vals))))

noncomputable def finishP : Procedure finishCode dynCode finishStep := by
  let seed := first seedCode (prodCode FlowMachine.flowCode valuesCode)
  let rest := second seedCode (prodCode FlowMachine.flowCode valuesCode)
  let mass := (first FlowMachine.flowCode valuesCode).comp rest
  let vals := (second FlowMachine.flowCode valuesCode).comp rest
  let src := sourceIndexP.comp seed
  let item := (listGet itemCode zeroItem).comp (src.pair vals)
  let routeIds := (second GridMachine.keyCode routeCode).comp item
  let newFlow := FlowMachine.updateP.comp (mass.pair routeIds)
  let fields := (second Nat.bits (prodCode (listCode boolCode) (prodCode intCode banksCode))).comp seed
  let signs := (first (listCode boolCode) (prodCode intCode banksCode)).comp fields
  let data := (second (listCode boolCode) (prodCode intCode banksCode)).comp fields
  let banks := (second intCode banksCode).comp data
  let experts := (first bankCode bankCode).comp banks
  let opts := (second bankCode bankCode).comp banks
  let m := (Learning.GenerationCost.lengthUnaryP intCode 0).comp experts
  let g := (Learning.GenerationCost.lengthUnaryP intCode 0).comp opts
  let cutoff := (listLength boolCode false).comp signs
  let zero := constant finishCode Nat.bits 0
  let left := blockP.comp (m.pair (zero.pair vals))
  let right := blockP.comp (g.pair (cutoff.pair vals))
  exact (newFlow.pair (left.pair right)).congrFun (fun _ => rfl)

/-- Typed frames on which the machine actually reads and writes. -/
def makeSeed (z : ℕ × Environment) : Seed :=
  (z.1,(z.2.1.2.1,(z.2.1.1,z.2.2.2)))

def makeRowsInput (z : ℕ × Environment) : FlowMachine.Rows.Raw :=
  (z.2.1.2,(z.2.2.1,terminalBanks (makeSeed z)))

def horizon (z : Environment) : ℕ := z.1.2.1.length + z.2.2.2.length - 1

def marketUnit (z : ℕ × Environment) : Dynamic :=
  let graph := FlowMachine.Rows.make (makeRowsInput z)
  let vals := GridMachine.Table.solve (horizon z.2,graph)
  finishStep (makeSeed z,(z.2.2.1,vals))

private noncomputable abbrev idP := first Nat.bits envCode
private noncomputable abbrev envP := second Nat.bits envCode
private noncomputable abbrev fixedP := first fixedCode dynCode
private noncomputable abbrev stateP := second fixedCode dynCode
private noncomputable abbrev Dp := (first intCode FlowMachine.Rows.statCode).comp fixedP
private noncomputable abbrev statP := (second intCode FlowMachine.Rows.statCode).comp fixedP
private noncomputable abbrev signP := (first FlowMachine.Rows.blist (prodCode FlowMachine.Rows.blist FlowMachine.Rows.ilist)).comp statP
private noncomputable abbrev massP := (first FlowMachine.flowCode banksCode).comp stateP
private noncomputable abbrev storedP := (second FlowMachine.flowCode banksCode).comp stateP

noncomputable def seedP : Procedure unitCode seedCode makeSeed :=
  idP.pair ((signP.comp envP).pair ((Dp.comp envP).pair (storedP.comp envP)))

noncomputable def buildRowsP : Procedure unitCode FlowMachine.Rows.rawCode makeRowsInput :=
  (statP.comp envP).pair ((massP.comp envP).pair (terminalBanksP.comp seedP))

noncomputable def horizonP : Procedure envCode unaryCode horizon := by
  let m := (Learning.GenerationCost.lengthUnaryP boolCode false).comp signP
  let opts := (second bankCode bankCode).comp storedP
  let g := (Learning.GenerationCost.lengthUnaryP intCode 0).comp opts
  exact (unaryPred.comp (unaryAdd.comp (m.pair g))).congrFun fun _ => rfl

/-- A single fixed bit-stack program combines all operations for an augmenting unit. -/
noncomputable def unitP : Procedure unitCode dynCode marketUnit := by
  let graph := FlowMachine.Rows.rowsP.comp buildRowsP
  let vals := GridMachine.Table.solveProgram.comp ((horizonP.comp envP).pair graph)
  exact (finishP.comp (seedP.pair ((massP.comp envP).pair vals))).congrFun (fun _ => rfl)

def marketDouble (x : Environment) : Dynamic := (x.2.1.map (2*·),x.2.2)

noncomputable def doubleP : Procedure envCode dynCode marketDouble :=
  (FlowMachine.doubleP.comp massP).pair storedP

/-- Action 0 doubles; positive action `j+1` increments expert `j`. -/
def action (z : ℕ × Environment) : Environment :=
  (z.2.1, if z.1 = 0 then marketDouble z.2 else marketUnit (z.1-1,z.2))

noncomputable def actionP : Procedure unitCode envCode action := by
  let zer := binaryZero.comp idP
  let pred := binarySub.comp (idP.pair (constant unitCode Nat.bits 1))
  let u := unitP.comp (pred.pair envP)
  let out := (choose u (doubleP.comp envP)).comp (zer.pair (identity unitCode))
  exact ((fixedP.comp envP).pair out).congrFun (by intro z; simp [action])

/-- Run the composed binary-stack program with its measured polynomial and its full output. -/
theorem action_deploy (o : OracleSpec.WordOracle) (z : ℕ × Environment) :
    (OracleSpec.BitCode.deploy actionP).ComputesWithin o (unitCode z)
      (3*actionP.bound.eval (unitCode z).length+2*(unitCode z).length+2)
      (fun history bits => history=[] ∧ bits = envCode (action z)) :=
  OracleSpec.BitCode.deploy_correct actionP o z

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
