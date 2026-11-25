import OAI.Hierarchy.PaperBoundsSpectralDescent
import OAI.ThreeFlat.SquareExponent
import OAI.ThreeFlat.RationalBound

namespace OAI
namespace Hierarchy
open LinearAlgebra.SpectralBooks ThreeFlat
noncomputable section

variable (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
    ¬HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
      Tagged.WidthReductions (ZMod p) k)
  (descent : ∀(p : ℕ) [Fact p.Prime], NonlinearExpanders.SpectralFamily (ZMod p) → CollapseOracle.Descent (ZMod p))
  (grid : ∀(p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → NonlinearExpanders.SpectralFamily (ZMod p) →
    GridTraceCompiler (ZMod p) k)

include width descent grid

/-- The same prime witnesses give the exact three-dimensional profile bound and its
rational certificate in both models of square matrix multiplication. -/
theorem three_flat_square_of_spectral_descent (F : Type*) [Field F] :
    let c:=2 / profileInv (1/3)
    (c≤formalOmega F 1 1 1 ∧ c≤divisionOmega F 1 1 1) ∧
    ((43:ℝ)/20≤formalOmega F 1 1 1 ∧ (43:ℝ)/20≤divisionOmega F 1 1 1) :=by
  have flat (p : ℕ) [Fact p.Prime] : HasSpectralFlat (ZMod p) 3 :=
    prime_flat_of_spectral_descent p (width p) (descent p) (grid p) 3
  have bound:=square_exponents_of_prime_threeFlats flat F
  exact ⟨bound,fortyThree_div_twenty_le_omegaThree.trans bound.1,
    fortyThree_div_twenty_le_omegaThree.trans bound.2⟩

end
end Hierarchy

end OAI
