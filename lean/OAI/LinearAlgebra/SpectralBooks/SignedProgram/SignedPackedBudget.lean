import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedPackedStep

/-! # Polynomial bound for a packed signed computation step -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

/-- The entire packed step, including row selection and every tape cell, uses
at most a fixed polynomial in the program input length and window radius. -/
theorem packedStep_count (n r : ℕ) :
    (packedStep n r).net.count ≤ 100000 * (n+r+2)^6 := by
  apply (packedStep_count_budget n r).trans
  rw [frameWire_card]
  unfold frameTickBitBudget lookupBitBudget rowMatchBudget packedStepSignalBudget
  ring_nf
  omega

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
