import OAI.Optimization.LinearProgramming.Recovery.WitnessExportCore
import OAI.Optimization.LinearProgramming.Elimination.UniformSolve

/-! The native rectangular solver's public result header supplies precisely the
coordinates copied by the witness export. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessExport

open RAM RAM.Callable

theorem program_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (native caller : Memory K)
    (hn : native.AllData P) (hc : caller.AllData P) (d dst : ℕ) (w : Fin d → K)
    (hdst : caller.index 210 = dst) (hd : caller.index 211 = d) (hbase : 5 ≤ dst)
    (hsol : Elimination.readSolutionFromHeader d native = some w) :
    ∃ t, program.Run P (Odd.memory native caller) (time d) (Odd.memory native t) ∧
      t.AllData P ∧ (∀ j : Fin d, t.data (dst+j.val) = w j) ∧
      (∀ p, 200 ≤ p → t.index p = caller.index p) ∧
      (∀ p, 5 ≤ p → (p < dst ∨ dst+d ≤ p) → t.data p = caller.data p) := by
  apply program_run_values P native caller hn hc d dst w hdst hd hbase
  unfold Elimination.readSolutionFromHeader at hsol
  split at hsol
  · exact congrFun (Option.some.inj hsol)
  · cases hsol

end WitnessExport
end Recovery
end LinearProgramming
end Optimization
end OAI
