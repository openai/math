import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveCode
import OAI.Optimization.LinearProgramming.Elimination.UniformBounds
import OAI.Optimization.LinearProgramming.Elimination.SolveEquiv
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableWindow

/-! A normal call of the fixed rectangular solver on an augmented tableau in the
caller's logical memory. The caller's high registers survive the invocation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessSolve

open RAM RAM.Callable
open OAI.Optimization.LinearProgramming.Geometry

theorem call_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (native caller : Memory ℚ) (src dimPtr cap oldCap M : ℕ)
    (raw : RawTapes caller src dimPtr cap (encodedGramInput (Elimination.augmentedRows A b)) [d+1,m])
    (foot : Footprint oldCap (native.atPC 0)) (fit : oldCap < cap)
    (cells : (d+1)*m ≤ cap) (dims : 2 ≤ cap)
    (oldSafe : native.AllData (fun q => ratBits q ≤ M))
    (callerSafe : caller.AllData (fun q => ratBits q ≤ M)) (three : 3 ≤ M)
    (height : solverHeight (totalBits (encodedGramInput (Elimination.augmentedRows A b))) ≤ M) :
    ∃ out, call.Run (fun q => ratBits q ≤ M) (Odd.memory native caller) (callTime d m cap)
        (Odd.memory out (caller.putIndex 1 0)) ∧
      Elimination.readSolutionFromHeader d out = Elimination.fixedSolve A b ∧
      out.AllData (fun q => ratBits q ≤ M) ∧
      Footprint (nativeWindow Elimination.uniformSolveProgram [d+1,m]
        (encodedGramInput (Elimination.augmentedRows A b)) + solverTime d m) (out.atPC 0) := by
  let xs := encodedGramInput (Elimination.augmentedRows A b)
  let P := fun q : ℚ => ratBits q ≤ M
  obtain ⟨k,hk,tr,run,halt,answer,safe⟩ := Elimination.uniformSolveProgram_bounds A b
  let out := (tr (Fin.last k)).memory
  have bounds (i : Fin (k+1)) (j : ℕ) : P ((tr i).data j) := (safe i j).trans height
  have performed := Odd.invoke_packed 1 (.index 1) P caller [d+1,m] xs tr
    (show 0<1 by decide) callerSafe run bounds halt
    (show (caller.putIndex 1 0).AllData P from callerSafe)
  have invoked := Fragment.stage_of_run (native.atPC 0) caller src dimPtr oldCap cap xs [d+1,m]
    raw callerSafe oldSafe three foot fit (by simpa [xs] using cells) (by simpa using dims) performed
  have work : k ≤ solverTime d m := hk
  refine ⟨out,invoked.mono ?_,answer.trans (Elimination.fixedSolve_eq_solve A b).symm,bounds (Fin.last k),?_⟩
  · unfold callTime
    omega
  · exact nativeWindow_trace run work

end WitnessSolve
end Recovery
end LinearProgramming
end Optimization
end OAI
