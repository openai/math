import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramOrder

/-! # A cubic bound for the packed decoder witness -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Hot

/-- Scalar equality flags, the body-length flag, and all cursor marks fit in cubic width. -/
theorem decodeGuessWidth_le_cubic (n : ℕ) : decodeGuessWidth n ≤ 100 * (n + 2) ^ 3 := by
  apply (decodeGuessWidth_le n).trans
  unfold slotsCount
  nlinarith only [Nat.zero_le n, Nat.zero_le (n ^ 2), Nat.zero_le (n ^ 3)]

end SignedProgram.Hot

end SpectralBooks
end LinearAlgebra
end OAI
