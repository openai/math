import OAI.Optimization.LinearProgramming.Elimination.UniformSolveBits
import OAI.Optimization.LinearProgramming.Elimination.UniformTimeBound

/-! Monomial time and bit bounds for the fixed finite rectangular-solver program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination
open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry Matrix

theorem solveLengthBits_bound (L : ℕ) : solveLengthBits L ≤ 1_000_000*(L+1)^6 := by
  dsimp [solveLengthBits,solveBits,dotBitBound,gramDetBits,detRegisterBits]
  nlinarith only [Nat.zero_le L,Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4),
    Nat.zero_le (L^5),Nat.zero_le (L^6)]

/-- The actual trace satisfies both conventional strong-polynomial resource inequalities. -/
theorem uniformSolveProgram_bounds {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m→ℚ) :
    let input:=encodedGramInput (augmentedRows A b)
    let L:=totalBits input
    ∃k ≤ 10_000_000_000*(d+m+1)^9,∃tr : Fin (k+1)→State ℚ,
      Trace uniformSolveProgram (start [d+1,m] input) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      readSolutionFromHeader d (tr (Fin.last k)).memory=solve A b ∧
      ∀i,scalarBound (1_000_000*(L+1)^6) (tr i) := by
  obtain ⟨k,hk,tr,ht,hh,_,out,hs⟩:=uniformSolveProgram_stronglyPolynomial A b
  exact ⟨k,hk.trans (solveTime_bound d m),tr,ht,hh,out,fun i p=>(hs i p).trans (solveLengthBits_bound _)⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
