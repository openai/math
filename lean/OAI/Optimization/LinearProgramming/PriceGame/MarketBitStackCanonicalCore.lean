import OAI.Optimization.LinearProgramming.PriceGame.MarketAugmentMachineStep
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackReadout
import OAI.Optimization.LinearProgramming.PriceGame.ControlScoreQuantize

/-! A fresh zero-terminal Bellman table computes the final dummy-normalized prices
from the optimal integral flow. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
namespace Readout

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Augment.Machine Table

def zeroRows (e : Environment) : FlowMachine.Rows.Raw :=
  (e.1.2,(e.2.1,(e.2.2.1.map (fun _ => 0),e.2.2.2.map (fun _ => 0))))

def goodAddresses (e : Environment) : List ℕ :=
  (List.range (e.2.2.2.length-1)).map fun j => e.1.2.1.length+(j+1)

/-- Each real good is represented by a reduced rational with the difference of its own Bellman score from
the dummy's Bellman score. -/
def canonical (e : Environment) : List ℚ :=
  let vals := Table.solve (horizon e,FlowMachine.Rows.make (zeroRows e))
  (goodAddresses e).map fun j => normalized (((e.1.1.toNat,vals),e.1.2.1.length),j)

private noncomputable abbrev stat := (second intCode FlowMachine.Rows.statCode).comp
  (first fixedCode dynCode)
private noncomputable abbrev signs := (first FlowMachine.Rows.blist
  (prodCode FlowMachine.Rows.blist FlowMachine.Rows.ilist)).comp stat
private noncomputable abbrev dyn := second fixedCode dynCode
private noncomputable abbrev banks := (second FlowMachine.flowCode banksCode).comp dyn
private noncomputable abbrev experts := (first bankCode bankCode).comp banks
private noncomputable abbrev options := (second bankCode bankCode).comp banks

noncomputable def zeroRowsP : Procedure envCode FlowMachine.Rows.rawCode zeroRows := by
  let zero := listMap (0 : ℤ) (0 : ℤ) (constant intCode intCode (0 : ℤ))
  let f := (first FlowMachine.flowCode banksCode).comp dyn
  exact stat.pair (f.pair ((zero.comp experts).pair (zero.comp options)))

noncomputable def goodAddressesP : Procedure envCode (listCode Nat.bits) goodAddresses := by
  let dom := prodCode unaryCode Nat.bits
  let step := binaryAdd.comp ((unaryToBits.comp (first unaryCode Nat.bits)).pair (constant dom Nat.bits 1))
  let addr := binaryAdd.comp ((second unaryCode Nat.bits).pair step)
  let n := unaryPred.comp ((Learning.GenerationCost.lengthUnaryP intCode 0).comp options)
  let m := (listLength boolCode false).comp signs
  exact ((tabulate (f := fun a j : ℕ => a+(j+1)) 0 addr).comp (n.pair m)).congrFun (fun _ => rfl)

noncomputable def canonicalP : Procedure envCode (listCode ratCode) canonical := by
  let d := Control.Native.intToNatP.comp ((first intCode FlowMachine.Rows.statCode).comp
    (first fixedCode dynCode))
  let vals := Table.solveProgram.comp (horizonP.pair (FlowMachine.Rows.rowsP.comp zeroRowsP))
  let m := (listLength boolCode false).comp signs
  exact (pricesP.comp (goodAddressesP.pair ((d.pair vals).pair m))).congrFun (fun _ => rfl)

theorem canonical_deploy (o : OracleSpec.WordOracle) (e : Environment) :
    (OracleSpec.BitCode.deploy canonicalP).ComputesWithin o (envCode e)
      (3*canonicalP.bound.eval (envCode e).length+2*(envCode e).length+2)
      (fun history bits => history=[] ∧ bits = listCode ratCode (canonical e)) :=
  OracleSpec.BitCode.deploy_correct canonicalP o e

end Readout
end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
