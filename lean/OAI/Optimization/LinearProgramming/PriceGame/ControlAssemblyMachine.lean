import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyLoops
import OAI.Optimization.LinearProgramming.PriceGame.ControlScoreQuantize
import OAI.Optimization.LinearProgramming.PriceGame.ControlListMedian
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTestMachine
import OAI.Optimization.LinearProgramming.OracleSpec.BitStack

/-! Binary-stack program for assembling a completed frame. The physical iteration counts
come from the expert array and the first final mapped row. The probe count occurs only
as a binary list cutoff and a rational denominator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost Trial Wire

noncomputable def framePricesP (r : ℕ) : Procedure assemblyFrameCode assemblyRowCode
    (fun x => (assembleValue r x).prices) := by
  let one := medianValueP.comp (finalColumnP r)
  let table := tabulate (f := priceAt r) (0 : ℚ) one
  exact table.comp ((outputWidthP r).pair (identity assemblyFrameCode))

noncomputable def isLocalAtP : Procedure (prodCode unaryCode assemblyFrameCode) boolCode
    (fun p => decide ((atD p.2.experts p.1).level = p.2.input.level)) := by
  let fr := second unaryCode assemblyFrameCode
  let idx := unaryToBits.comp (first unaryCode assemblyFrameCode)
  let ex := (atDP packedExpertCode).comp (idx.pair (frameRosterP.comp fr))
  let exlevel := Learning.BitMachine.expertLevelP.comp ex
  let level := nodeLevelP.comp (frameInputP.comp fr)
  exact natEqP.comp (exlevel.pair level)

noncomputable def frameScoreAtP (r : ℕ) : Procedure (prodCode unaryCode assemblyFrameCode) Nat.bits
    (fun p => scoreAt r p.2 p.1) := by
  let env := prodCode unaryCode assemblyFrameCode
  let gainTotal := ratListSumP.comp (gainColumnP r)
  let localMean := ratDiv.comp (gainTotal.pair (constant env ratCode (r : ℚ)))
  let casts := (listMap 0 0 natToRat).comp scoreColumnP
  let deepTotal := ratListSumP.comp casts
  let deepMean := ratDiv.comp (deepTotal.pair (constant env ratCode ((2*r : ℕ) : ℚ)))
  let select := conditional isLocalAtP (scoreP.comp localMean) (scoreP.comp deepMean)
  apply select.congrFun
  rintro ⟨e,x⟩
  change (if decide ((atD x.experts e).level = x.input.level) then
    Moment.rationalScore Moment.scaleQ Moment.sigmaQ
      (((x.calls.take r).map fun c => atD c.gains e).sum / (r : ℚ)) else
    Moment.rationalScore Moment.scaleQ Moment.sigmaQ
      (((x.calls.map fun c => atD c.child.scores e).map (fun n : ℕ => (n : ℚ))).sum /
        ((2*r : ℕ) : ℚ))) = _
  simp only [scoreAt, decide_eq_true_eq, List.map_map, Function.comp_def]

noncomputable def frameScoresP (r : ℕ) : Procedure assemblyFrameCode (listCode Nat.bits)
    (fun x => (assembleValue r x).scores) :=
  (tabulate (f := scoreAt r) 0 (frameScoreAtP r)).comp
    (outputRosterLengthP.pair (identity assemblyFrameCode))

/-- One finite stack program physically produces all three return arrays, including
every logged price and each nested child log. Its `runs` field includes a polynomial
clock on every encoded input frame. -/
noncomputable def assembleFrameP (r : ℕ) : Procedure assemblyFrameCode packedRoundCode
    (assembleValue r) :=
  ((framePricesP r).pair ((frameScoresP r).pair (frameLogP r))).result (fun _ => rfl)

/-- The saved control frame supplies the roster, node input and completed calls in order. -/
noncomputable def assembleFieldsP (r : ℕ) :
    Procedure (prodCode assemblyRosterCode (prodCode nodeInputCode assemblyCallsCode)) packedRoundCode
      (fun p => assembleValue r ⟨p.1,p.2.1,p.2.2⟩) :=
  (assembleFrameP r).precompose (fun p : List PackedExpert × NodeInput × List Completed =>
    ⟨p.1, p.2.1, p.2.2⟩)

theorem assembleFrameP_runs (r : ℕ) (frame : AssemblyFrame) :
    ∃ steps ≤ (assembleFrameP r).bound.eval (assemblyFrameCode frame).length,
      Runs (assembleFrameP r).program (singletonStore (assembleFrameP r).input (assemblyFrameCode frame))
        (singletonStore (assembleFrameP r).output (packedRoundCode (assembleValue r frame))) steps :=
  (assembleFrameP r).runs frame

/-- Embed the same finite control in an oracle machine, preserving the current query
buffer and transcript and charging the original polynomial running time. -/
theorem assembleFrameP_exec (r k : ℕ) (embed : (assembleFrameP r).K ↪ Fin k)
    (base : Store (Fin k)) (answer : Fin k) (o : OracleSpec.WordOracle)
    (buf : OracleSpec.Word) (hist : OracleSpec.Transcript) (frame : AssemblyFrame) :
    ∃ steps ≤ (assembleFrameP r).bound.eval (assemblyFrameCode frame).length,
      OracleSpec.BitCode.Executes answer o
        (OracleSpec.BitCode.ofBitStack ((assembleFrameP r).program.relabel embed))
        ⟨overlay embed base (singletonStore (assembleFrameP r).input (assemblyFrameCode frame)), buf, hist⟩
        ⟨overlay embed base (singletonStore (assembleFrameP r).output
          (packedRoundCode (assembleValue r frame))), buf, hist⟩ steps :=
  OracleSpec.BitCode.procedure_exec (assembleFrameP r) embed base answer o buf hist frame

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
