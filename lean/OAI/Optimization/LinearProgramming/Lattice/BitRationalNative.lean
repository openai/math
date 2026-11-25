import OAI.Optimization.LinearProgramming.Lattice.BitRationalRows
import OAI.Optimization.LinearProgramming.Lattice.LLLBitNative

/-! One polynomial-clocked finite bit program for arbitrary rational LLL input. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit

open ExactQuantumFactoring.BitStackProgram

noncomputable def lllRatRows : RatMatrix → RatMatrix := lllRatRowsWith lllRows

noncomputable def lllRatRowsP : Procedure ratMatrixCode ratMatrixCode lllRatRows :=
  lllRatRowsWithP lllRowsP

theorem lllRatRows_pack {p n : ℕ} (A : Matrix (Fin (p+1)) (Fin n) ℚ)
    (ha : LinearIndependent ℝ (fun i => euclideanRow (A i))) :
    lllRatRows (Selector.packedTable A) = Selector.packedTable (reduceRational A) :=
  lllRatRowsWith_pack lllRows A ha (fun b hb => lllRows_packMatrix b (by omega) hb)

end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
