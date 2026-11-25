import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import OAI.Optimization.LinearProgramming.Specification
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Independent ordinary-input interface between the marked-subspace RAM and the
LP search-to-witness reduction. Its dimensions, tape, outputs and two bounds are
specified without referring to either implementation. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NormalSubspace
open Matrix RAM OracleSpec
open scoped Matrix

def inputSize {r s : ℕ} (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ) : ℕ :=
  r+s+((MinorLog.entries D++MinorLog.entries E).map ratBits).sum

structure Spec where
  program : Program
  clock : Polynomial ℕ
  height : Polynomial ℕ
  run : ∀ (r s : ℕ) (hn : 0 < r+s) (D : Matrix (Fin r) (Fin (r+s)) ℚ) (E : Matrix (Fin s) (Fin (r+s)) ℚ),
    LinearIndependent ℚ D.row → LinearIndependent ℚ E.row → D*Eᵀ=0 →
    ∃ k ≤ clock.eval (r+s),∃ tr : Fin (k+1)→State ℚ,
      Trace program (start [r,s] (MinorLog.entries D++MinorLog.entries E)) k tr ∧
      (∃ answer : Bool,(tr (Fin.last k)).output=some answer.toNat ∧
        (answer=true ↔ ∃x∈Submodule.span ℚ (Set.range D.row),0 ≤ x ∧ 0 < x ⟨0,hn⟩)) ∧
      ∀ i j,ratBits ((tr i).data j) ≤ height.eval (inputSize D E)

end NormalSubspace
end LinearProgramming
end Optimization
end OAI
