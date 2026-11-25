import OAI.Hierarchy.NativePaperBounds
import OAI.Hierarchy.TaggedRadixPacking

namespace OAI
/-! # All-field arithmetic bounds using the constructed physical radix packing -/
namespace Hierarchy
open LinearAlgebra.SpectralBooks

variable (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
    ¬HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
      Tagged.WidthReductions (ZMod p) k)
  (layer : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
  (grid : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k →
    NonlinearExpanders.SpectralFamily (ZMod p) → GridTraceCompiler (ZMod p) k)

include width layer grid

theorem paper_bounds_after_radix (F : Type*) [Field F] :
    (VF F ⊂ VBP F ∧ VBP F ⊂ VP F ∧ VP F ⊂ VNP F) ∧
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤formalOmega F 1 1 1 ∧
    (1097:ℝ)/500<formalOmega F 1 1 1 := by
  apply paper_bounds_of_native_constructions _ layer grid F
  intro p _ k hk flat miss family
  exact ⟨Tagged.Radix.packing_bound,width p k hk flat miss family⟩

theorem division_exponent_after_radix (F : Type*) [Field F] :
    2*Real.exp (stdNormalQuantile (2/3)^2/2)≤divisionOmega F 1 1 1 ∧
    (1097:ℝ)/500<divisionOmega F 1 1 1 := by
  rw [divisionOmega_square_eq_formalOmega]
  exact (paper_bounds_after_radix width layer grid F).2

end Hierarchy

end OAI
