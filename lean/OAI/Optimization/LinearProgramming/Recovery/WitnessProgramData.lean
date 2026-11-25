import OAI.Optimization.LinearProgramming.Recovery.EquationWitness
import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases
import OAI.Optimization.LinearProgramming.Elimination.Augmented

/-! The marked system, its right-hand side, and the row-major augmented tableau over a field. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessProgram

def system {K : Type*} [Field K] {h n : ℕ} (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) (hn : 0<n) :
    Matrix (Fin (h+n+1)) (Fin n) K :=
  normalizedSystem (maskedEquations E S) ⟨0,hn⟩

def rhs {K : Type*} [Field K] (h n : ℕ) : Fin (h+n+1) → K := Presentation.anchorRhs (h+n)

def tableau {K : Type*} [Field K] {h n : ℕ} (E : Matrix (Fin h) (Fin n) K) (S : Finset (Fin n)) (hn : 0<n) :
    Matrix (Fin (n+1)) (Fin (h+n+1)) K :=
  Elimination.augmentedRows (system E S hn) (rhs h n)

end WitnessProgram
end Recovery
end LinearProgramming
end Optimization
end OAI
