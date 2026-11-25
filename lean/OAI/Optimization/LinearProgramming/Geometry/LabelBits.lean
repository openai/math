import OAI.Optimization.LinearProgramming.Geometry.PivotBasis
import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeDenominator
import OAI.Optimization.LinearProgramming.Compression.PowerBits

/-! Dimension-only bounds on the rounded projection data and its common
denominator. The coefficients at unrequested minors never enter these bounds. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open Matrix Finset SignType RAM
open scoped BigOperators Matrix

variable {r n : ℕ}

private theorem bits_nat_le {q k : ℕ} (h : q ≤ 2 ^ k) : ratBits (q : ℚ) ≤ 3+k := by
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast]
  change 3 + q.log2 + 0 ≤ 3 + k
  have := log2_le_of_le_two_pow h
  omega

theorem roundedPower_ratBits (θ : ℚ) (B : ℕ) : ratBits (roundedPower θ B) ≤ 2*(B+4) := by
  have hn := bits_nat_le (roundedPowerNumerator_le θ B)
  have hd : ratBits ((2 : ℚ)^(B+1)) ≤ 3+(B+1) := by
    simpa using (bits_nat_le (Nat.le_refl (2^(B+1))))
  unfold roundedPower
  rw [div_eq_mul_inv]
  refine (Compression.ratBits_mul_le_add _ _).trans ?_
  rw [Compression.ratBits_inv_eq]
  omega

theorem roundedPivotMatrix_ratBits (rows : Fin r → PivotRow n) (t : Fin n → ℚ)
    (B : ℕ) (i : Fin r) (j : Fin n) :
    ratBits (roundedPivotMatrix rows t B i j) ≤ 8 + 2*(B+4) := by
  have hs (a : SignType) : ratBits ((a : ℚ)) ≤ 4 := by
    cases a <;> decide
  change ratBits (_ * _ * roundedPower _ B) ≤ _
  exact (Compression.ratBits_mul_le_add _ _).trans <|
    (Nat.add_le_add ((Compression.ratBits_mul_le_add _ _).trans (Nat.add_le_add (hs _) (hs _)))
      (roundedPower_ratBits _ B)).trans (by omega)

/-- Entries fed to the rational separation routine have a bit bound calculated solely
from the dimensions, even when the original determinants have arbitrarily many bits. -/
theorem roundedGramProjector_ratBits (rows : Fin r → PivotRow n) (t : Fin n → ℚ)
    (B : ℕ) (i j : Fin n) :
    ratBits (computeGramProjector (roundedPivotMatrix rows t B) i j) ≤
      gramProjectorBits r n (8 + 2*(B+4)) :=
  computeGramProjector_bits _ (roundedPivotMatrix_ratBits rows t B) i j

end Geometry
end LinearProgramming
end Optimization
end OAI
