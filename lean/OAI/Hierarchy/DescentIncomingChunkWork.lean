import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # Cost of a dense or partially filled packed group row -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup
/-- A completely occupied-width group which fits in one hardware chunk is already
covered by the per-host word, even if the shift was capped by the number of groups. -/
theorem chunk_work_or (H G M word short : ℕ) (fits : G≤M ∨ word≤M*short) :
    (H*chunks G M)*word ≤ H*word+H*G*short :=by
  rcases fits with fits|fill
  · by_cases zero : M=0
    · have z : G=0 :=by omega
      simp [z,zero,chunks,ThreeFlat.Routing.poolBatchCount]
    · have atMost : chunks G M≤1 :=by
        apply Nat.le_of_lt_succ
        change (G+M-1)/M<2
        exact (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      have rows:=Nat.mul_le_mul_right word (Nat.mul_le_mul_left H atMost)
      exact (by simpa using rows : H*chunks G M*word≤H*word).trans (Nat.le_add_right ..)
  · exact chunk_work H G M word short fill

end Hierarchy.DescentDatedSeedStartup

end OAI
