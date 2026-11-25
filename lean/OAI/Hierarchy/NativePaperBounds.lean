import OAI.Hierarchy.FlatDiagonal
import OAI.Hierarchy.SeparationFromFlats
import OAI.Hierarchy.SquareDivisionExponent

namespace OAI
/-! # Arithmetic consequences of the three constructions of the flat argument -/

namespace Hierarchy

open LinearAlgebra.SpectralBooks

/-- The graph witnesses, scalar extension, and passage to the limiting normal
quantile introduce no premises beyond the three native constructions. -/
theorem paper_bounds_of_native_constructions
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
      ¬ HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
        Tagged.RadixBound (ZMod p) k ∧ Tagged.WidthReductions (ZMod p) k)
    (layer : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
    (compiler : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k →
      NonlinearExpanders.SpectralFamily (ZMod p) → GridTraceCompiler (ZMod p) k)
    (F : Type*) [Field F] :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2 * Real.exp (stdNormalQuantile (2 / 3) ^ 2 / 2) ≤ formalOmega F 1 1 1 ∧
    (1097 : ℝ)/500 < formalOmega F 1 1 1 := by
  apply paper_bounds_of_spectral_flats _ F
  apply UnboundedPrimeFieldFlats.of_all
  intro p _ d _
  exact all_flats_of_native_constructions width layer compiler (ZMod p) d


/-- The same construction bounds admissible formal scalar circuits that can
divide, also in positive characteristic. -/
theorem division_exponent_of_native_constructions
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
      ¬ HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
        Tagged.RadixBound (ZMod p) k ∧ Tagged.WidthReductions (ZMod p) k)
    (layer : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
    (compiler : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k →
      NonlinearExpanders.SpectralFamily (ZMod p) → GridTraceCompiler (ZMod p) k)
    (F : Type*) [Field F] :
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤divisionOmega F 1 1 1 ∧
    (1097:ℝ)/500<divisionOmega F 1 1 1 := by
  rw [divisionOmega_square_eq_formalOmega]
  exact (paper_bounds_of_native_constructions width layer compiler F).2


end Hierarchy

end OAI
