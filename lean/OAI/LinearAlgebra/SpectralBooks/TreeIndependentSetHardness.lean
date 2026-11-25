import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedPackedBudget
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedVerifierFamily
import OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph.IntegralIndependentSetFamily
import OAI.LinearAlgebra.SpectralBooks.TreeProfileShortening
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramParser

/-! # The signed universal verifier and independent-set hardness in the Tree case

The circuit checks a unique program encoding and unrolls the original clock.
Its signed counts are the coefficients of the specified integral family.
Consequently the graph lower bound follows directly from the companion's
border-stretch implication for a two-dimensional shortening.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Filter
open SignedProgram

/-- The signed verifier is a concrete family of bounded-fan-in Boolean circuits. -/
theorem polynomialSignedVerifier : BooleanChoice.PolynomialSignedVerifier := by
  apply polynomialSignedVerifier_of_fullVerifier Hot.parseNet packedStep
    (P := 1000000) (a := 6) (C := 100000) (b := 6)
  · exact Eventually.of_forall Hot.parseNet_count
  · exact Eventually.of_forall fun n r _ => packedStep_count n r
  · apply Eventually.of_forall
    intro n x
    apply fullVerifier_coefficient (packedStep n) (Hot.parseNet n) Hot.tableOfBits
    · exact fun _ _ h => Hot.parseNet_decode h
    · intro y p hp
      obtain ⟨g,⟨hg,_⟩,_⟩ := (Hot.unique_parse y p).mp hp
      exact ⟨g,hg,fun _ h => Hot.parse_guesses_equal h hg⟩
    · exact fun y g hg _ b f hf => packedStep_eval y g b f (Hot.parseNet_wellCoded hg) hf

/-- The concrete universal verifier transfers the degree-component border-size
stretch to homogeneous bipartite independent-set polynomials of maximum degree three. -/
theorem hardSubcubicGrids_of_witness_stretch {F : Type*} [Field F] {ε : ℝ}
    (hε : 0 < ε) (hard : SignedWitnessHardness F ε) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ :=
  BooleanChoice.hardSubcubicGrids_of_signedVerifier polynomialSignedVerifier hε hard

/-- A Tree wire metric gives the two-dimensional profiled shortening. Applying
the signed-witness border-stretch theorem yields the hard graph family. -/
theorem hardSubcubicGrids_of_shortening_stretch {F : Type*} [Field F]
    (tree : ¬ HasNonTreeWireMetric F)
    (stretch : Crossing.HasProfileShortening F 2 → ∃ ε : ℝ, 0 < ε ∧ SignedWitnessHardness F ε) :
    ∃ δ : ℝ, 0 < δ ∧ HardSubcubicGrids F δ := by
  obtain ⟨ε,hε,hard⟩ := stretch (hasProfileShortening_of_tree tree)
  exact hardSubcubicGrids_of_witness_stretch hε hard

/-- The same graphs work in every field, with stretch exponents transferred
through one absolute polynomial growth exponent. -/
theorem exists_integral_gridFamily :
    ∃ (b : ℕ) (G : (N : ℕ) → SubcubicGrid N), 0 < b ∧
      ∀ (F : Type*) [Field F] {ε δ : ℝ}, 0 < ε → 0 < δ → δ < ε / b → SignedWitnessHardness F ε →
        ∀ᶠ N : ℕ in atTop, DegreeBorderSizeAtLeast N ((2:ℝ)^((N:ℝ)^δ))
          (IndependentSetGrid.polynomial (R := F) (G N).edge) :=
  IndependentSetGraph.exists_gridFamily_of_signedVerifier polynomialSignedVerifier

end SpectralBooks
end LinearAlgebra
end OAI
