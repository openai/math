import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineOutputSpec
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineOutputProgram
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackCanonical
import OAI.Optimization.LinearProgramming.PriceGame.MarketInputSize

/-! A single fixed finite bit program writes the final output of the balanced market
solver, including the fresh canonical potential and all zero-quantity choices. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open Augment Augment.Machine
open ExactQuantumFactoring.BitStackProgram

variable {m g : ℕ}

theorem output_pack (I : Input m g) (qty : Fin m → ℕ) (D : ℕ) (s : State m g) (hd : 0 < D)
    (hc : ∀ e j, I.accepts e j → NumberBounds.OnGrid D (I.intercept e j)) :
    let out := outputFromFlow I.positive qty I.available I.intercept s.flow
    output (List.ofFn qty,packEnv I D s) = (List.ofFn out.1,packedCells out.2) :=
  finish_pack I qty D s hd hc _ (GridMachine.Readout.canonical_eq I D s hd hc)

theorem output_deploy_pack (I : Input m g) (qty : Fin m → ℕ) (D : ℕ) (s : State m g) (hd : 0 < D)
    (hc : ∀ e j, I.accepts e j → NumberBounds.OnGrid D (I.intercept e j)) (o : OracleSpec.WordOracle) :
    let data := argumentCode (List.ofFn qty,packEnv I D s)
    let out := outputFromFlow I.positive qty I.available I.intercept s.flow
    (OracleSpec.BitCode.deploy outputP).ComputesWithin o data
      (3*outputP.bound.eval data.length+2*data.length+2)
      (fun hist bits => hist=[] ∧ bits=answerCode (List.ofFn out.1,packedCells out.2)) :=
  finish_deploy_pack I qty D s hd hc GridMachine.Readout.canonicalP
    (GridMachine.Readout.canonical_eq I D s hd hc) o

/-- Specializing to the actual denominator of the intercept table discharges all grid
assumptions and gives the published balanced-output coding of the deterministic solver. -/
theorem output_computeWithDenominator (pos : Fin m → Bool) (L : Fin m → ℚ)
    (available : Fin m → Fin g → Bool) (c : Fin m → Fin g → ℚ) (Q : ℕ)
    (o : OracleSpec.WordOracle) :
    let I : Input m g := ⟨pos,available,c⟩
    let qty k := Denominator.qty Q (L k)
    let D := Denominator.denominator (NumberBounds.arcInput I)
    let data := argumentCode (List.ofFn qty,packEnv I D (I.solve qty))
    let out := computeWithDenominator pos L available c Q
    (OracleSpec.BitCode.deploy outputP).ComputesWithin o data
      (3*outputP.bound.eval data.length+2*data.length+2)
      (fun hist bits => hist=[] ∧ bits=answerCode (List.ofFn out.1,packedCells out.2)) := by
  let I : Input m g := ⟨pos,available,c⟩
  let qty k := Denominator.qty Q (L k)
  let D := Denominator.denominator (NumberBounds.arcInput I)
  have hd : 0 < D := Denominator.denominator_pos _
  have hc (e : Fin m) (j : Fin g) (_ : I.accepts e j) : NumberBounds.OnGrid D (I.intercept e j) :=
    (NumberBounds.grid_iff_den_dvd hd _).mpr (Denominator.den_dvd_denominator (NumberBounds.arcInput I) (e,j))
  exact output_deploy_pack I qty D (I.solve qty) hd hc o

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
