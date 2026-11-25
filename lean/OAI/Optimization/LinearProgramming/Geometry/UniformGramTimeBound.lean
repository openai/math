import OAI.Optimization.LinearProgramming.Geometry.UniformGramCore

/-! Polynomial runtime bounds for the Gram core and its optional input loader. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression

/-- Runtime of input materialization, Gram computation, and terminal instruction. -/
theorem uniformGramTotalTime {r n i j : ℕ} (hi : i ≤ 200*(r+n+1)^2) (hj : j ≤ uniformGramTime r n) :
    i+j+1 ≤ 5000000*(r+n+1)^9 := by
  let z := r+n+1
  have hr : r ≤ z := by dsimp [z]; omega
  have hn : n ≤ z := by dsimp [z]; omega
  have hz : 1 ≤ z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k ≤ 9) : z^k ≤ z^9 := Nat.pow_le_pow_right hz hk
  have hmono : uniformGramTime r n ≤ uniformGramTime z z := by
    dsimp only [uniformGramTime,gramTransposeTime,rowPhaseTime,gramInverseTime,
      uniformTableTime,uniformEntryTime,uniformRowDotCost,uniformCofactorTime]
    gcongr
  have h := Nat.add_le_add_right (Nat.add_le_add hi (hj.trans hmono)) 1
  apply h.trans
  change 200*z^2+uniformGramTime z z+1 ≤ 5000000*z^9
  dsimp only [uniformGramTime,gramTransposeTime,rowPhaseTime,gramInverseTime,
    uniformTableTime,uniformEntryTime,uniformRowDotCost,uniformCofactorTime]
  nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide),
    hp 4 (by decide),hp 5 (by decide),hp 6 (by decide),hp 7 (by decide),hp 8 (by decide)]

theorem uniformGramTime_bound (r n : ℕ) : uniformGramTime r n ≤ 5000000*(r+n+1)^9 := by
  have h := uniformGramTotalTime (r:=r) (n:=n) (i:=0) (j:=uniformGramTime r n) (Nat.zero_le _) le_rfl
  omega

end Geometry
end LinearProgramming
end Optimization
end OAI
