import OAI.Optimization.LinearProgramming.Geometry.PivotStageRAM

/-! Explicit monomial majorants for composing the numeric pivot routine with the label RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace PivotStageRAM

/-- The local width increment consists of a quartic signed-power calculation per
column. In particular it never raises the widths of pre-existing scratch to a power. -/
theorem widthIncrement_le (n L B : ℕ) : widthIncrement n L B ≤ 200000000000000*(n+L+B+1)^5 := by
  let S := n+L+B+1
  have pos : 0 < S := by simp [S]
  have bn : n ≤ S := by dsimp [S]; omega
  have linear : scoreWidth L ≤ 7*S := by dsimp [S,scoreWidth]; omega
  have inner : B+(9+10*scoreWidth L)+20 ≤ 64*S := by dsimp [S,scoreWidth]; omega
  have fourth : (B+(9+10*scoreWidth L)+20)^4 ≤ 16777216*S^4 := by
    calc _ ≤ (64*S)^4 := Nat.pow_le_pow_left inner 4
         _ = _ := by ring
  have one4 : 1 ≤ S^4 := by simpa using Nat.pow_le_pow_left (show 1 ≤ S by omega) 4
  have lin4 : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right pos (show 1 ≤ 4 by decide)
  have lin5 : S ≤ S^5 := by simpa only [pow_one] using Nat.pow_le_pow_right pos (show 1 ≤ 5 by decide)
  have signed : PowerRAM.signedWidth 0 (scoreWidth L) B ≤ 190000000000000*S^4 := by
    dsimp [PowerRAM.signedWidth]
    omega
  have all : n*PowerRAM.signedWidth 0 (scoreWidth L) B ≤ 190000000000000*S^5 := by
    calc _ ≤ S*(190000000000000*S^4) := Nat.mul_le_mul bn signed
         _ = _ := by ring
  change scoreWidth L+n*PowerRAM.signedWidth 0 (scoreWidth L) B ≤ 200000000000000*S^5
  omega

/-- The emitted scan, rounding and halt have a quadratic dimension/precision cost. -/
theorem stageCost_le (n B : ℕ) : n*(32*B+206)+18 ≤ 256*(n+B+1)^2 := by
  nlinarith [Nat.zero_le (n*n),Nat.zero_le (B*B),Nat.zero_le (n*B)]

end PivotStageRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
