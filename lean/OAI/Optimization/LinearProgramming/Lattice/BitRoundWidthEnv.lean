import OAI.Optimization.LinearProgramming.Lattice.BitRoundWidthCore
import OAI.Optimization.LinearProgramming.Lattice.BitRoundCodes

/-! Width of the persistent adaptive-rounding environment before any projector is run. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace RoundWidth
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

theorem env_length {p M fuel : ℕ} (old : List (Fin p → ℤ)) (hlen : old.length ≤ p)
    (hf : fuel ≤ p) (hd : DirectionBounds M old) :
    (Driver.envCode (((p,M),fuel),old.map List.ofFn)).length ≤ envBound.eval (parameter p M) := by
  have ht := table_length old hlen hd
  have hp := dim_le p M
  have hM : M.size ≤ parameter p M := by unfold parameter; omega
  simp only [Driver.envCode,Driver.inputCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
    Nat.size_eq_bits_len,envBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

end RoundWidth
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
