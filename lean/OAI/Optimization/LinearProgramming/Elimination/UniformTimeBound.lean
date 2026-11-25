import OAI.Optimization.LinearProgramming.Elimination.UniformSolve
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-! The dimension-only count for the ordinary rectangular solver over every ordered field. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination
open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry

theorem solveTime_bound (d m : ℕ) : solveTime d m ≤ 10_000_000_000*(d+m+1)^9 := by
  let z:=d+m+1
  have hd:d ≤ z := by dsimp [z];omega
  have hm:m ≤ z := by dsimp [z];omega
  have hz:1 ≤ z := by dsimp [z];omega
  have hp (j : ℕ) (hj:j ≤ 9) : z^j ≤ z^9 := Nat.pow_le_pow_right hz hj
  have hmono : solveTime d m ≤ solveTime z z := by
    dsimp only [solveTime,solveCoreTime,rowBasisTime,basisScanCost,basisProbeCost,decisionCost,maskTableCost,
      clearFlagsCost,gramInverseTime,inverseVectorTime,uniformCofactorTime,uniformTableTime,uniformEntryTime,uniformRowDotCost]
    gcongr
  apply hmono.trans
  change solveTime z z ≤ 10_000_000_000*z^9
  dsimp only [solveTime,solveCoreTime,rowBasisTime,basisScanCost,basisProbeCost,decisionCost,maskTableCost,
    clearFlagsCost,gramInverseTime,inverseVectorTime,uniformCofactorTime,uniformTableTime,uniformEntryTime,uniformRowDotCost]
  nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),hp 4 (by decide),
    hp 5 (by decide),hp 6 (by decide),hp 7 (by decide),hp 8 (by decide)]

end Elimination
end LinearProgramming
end Optimization
end OAI
