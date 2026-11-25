import OAI.Optimization.LinearProgramming.Recovery.WitnessSolveCall
import OAI.Optimization.LinearProgramming.Recovery.WitnessExport

/-! Invoke rectangular elimination on a caller-supplied augmented tape and keep
the resulting vector in the caller's designated high scalar window. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessSolve

open RAM RAM.Callable
open OAI.Optimization.LinearProgramming.Geometry

/-- The input is already in row-major augmented form. The native footprint is
returned so that the caller may stage another normal solver afterwards. -/
theorem program_run {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (native caller : Memory ℚ) (src dimPtr cap oldCap dst M : ℕ)
    (raw : RawTapes caller src dimPtr cap (encodedGramInput (Elimination.augmentedRows A b)) [d+1,m])
    (foot : Footprint oldCap (native.atPC 0)) (fit : oldCap < cap)
    (cells : (d+1)*m ≤ cap) (dims : 2 ≤ cap)
    (oldSafe : native.AllData (fun q => ratBits q ≤ M))
    (callerSafe : caller.AllData (fun q => ratBits q ≤ M)) (three : 3 ≤ M)
    (height : solverHeight (totalBits (encodedGramInput (Elimination.augmentedRows A b))) ≤ M)
    (destination : caller.index 210 = dst) (length : caller.index 211 = d) (separate : 5 ≤ dst)
    (w : Fin d → ℚ) (success : Elimination.fixedSolve A b = some w) :
    ∃ out next, program.Run (fun q => ratBits q ≤ M) (Odd.memory native caller) (time d m cap)
        (Odd.memory out next) ∧ out.AllData (fun q => ratBits q ≤ M) ∧
      next.AllData (fun q => ratBits q ≤ M) ∧ (∀ j : Fin d, next.data (dst+j.val) = w j) ∧
      (∀ i, 200 ≤ i → next.index i = caller.index i) ∧
      (∀ i, 5 ≤ i → (i < dst ∨ dst+d ≤ i) → next.data i = caller.data i) ∧
      Footprint (nativeWindow Elimination.uniformSolveProgram [d+1,m]
        (encodedGramInput (Elimination.augmentedRows A b)) + solverTime d m) (out.atPC 0) := by
  let P := fun q : ℚ => ratBits q ≤ M
  obtain ⟨out,entered,answer,safe,nextFoot⟩ := call_run A b native caller src dimPtr cap oldCap M raw foot
    fit cells dims oldSafe callerSafe three height
  have dstWord : (caller.putIndex 1 0).index 210 = dst :=
    (Memory.putIndex_ne caller (by decide : 210 ≠ 1) 0).trans destination
  have lenWord : (caller.putIndex 1 0).index 211 = d :=
    (Memory.putIndex_ne caller (by decide : 211 ≠ 1) 0).trans length
  obtain ⟨next,exported,nextSafe,output,indices,scalars⟩ :=
    WitnessExport.program_run P out (caller.putIndex 1 0) safe callerSafe d dst w dstWord lenWord separate
      (answer.trans success)
  refine ⟨out,next,entered.seq exported,safe,nextSafe,output,?_,scalars,nextFoot⟩
  intro i hi
  exact (indices i hi).trans (Memory.putIndex_ne caller (by omega : i ≠ 1) 0)

end WitnessSolve
end Recovery
end LinearProgramming
end Optimization
end OAI
