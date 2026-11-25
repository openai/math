import OAI.Optimization.LinearProgramming.Geometry.BorderBatchInput

/-! Dimension and entry-size bounds of the concrete determinant-and-reply batch. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM

theorem batchTime_formula_bound (r n : ℕ) :
    41*(r+n+1)^2+(n*(2200*(n+1)^7+17)+2)+(n*(6*r+60+n*(8*r+16)+2*n+2)+6) ≤
      polyBound 2600 8 (r+n) := by
  let z := r+n+1
  have hz : 0<z := by simp [z]
  have hr : r ≤ z := by dsimp [z]; omega
  have hn : n ≤ z := by dsimp [z]; omega
  have hn' : n+1 ≤ z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k≤8) : z^k≤z^8 := Nat.pow_le_pow_right hz hk
  calc
    _ ≤ 41*z^2+(z*(2200*z^7+17)+2)+(z*(6*z+60+z*(8*z+16)+2*z+2)+6) := by
      gcongr
    _ ≤ 2600*z^8 := by nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide)]

theorem batchLocalWidth_bound (r n E G : ℕ) :
    batchLocalWidth n E G ≤ polyBound 10 4 (r+n+E+G) := by
  let z := r+n+E+G+1
  have hz : 0<z := by simp [z]
  have hn : n≤z := by dsimp [z]; omega
  have he : E≤z := by dsimp [z]; omega
  have hg : G≤z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k≤4) : z^k≤z^4 := Nat.pow_le_pow_right hz hk
  calc
    _ ≤ z+z+(3+z^2+z*z+2*z*z^3) := by unfold batchLocalWidth; gcongr
    _ ≤ 10*z^4 := by nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide)]

theorem batchIncrement_bound (r n E G : ℕ) :
    batchIncrement n E G ≤ polyBound 40 4 (r+n+E+G) := by
  let z := r+n+E+G+1
  have hz : 0<z := by simp [z]
  have hn : n≤z := by dsimp [z]; omega
  have he : E≤z := by dsimp [z]; omega
  have hg : G≤z := by dsimp [z]; omega
  have hp (k : ℕ) (hk : k≤4) : z^k≤z^4 := Nat.pow_le_pow_right hz hk
  calc
    _ ≤ 3+(z+z+2*z*z^2+3)*(z+2)+z+z+6 := by unfold batchIncrement Compression.detRegisterBits; gcongr
    _ ≤ 40*z^4 := by nlinarith only [hp 0 (by decide),hp 1 (by decide),hp 2 (by decide),hp 3 (by decide)]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
