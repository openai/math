import OAI.Computability.NearSquareRoot.SynchronizedDilationPairs
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Explicit phase and Walsh matrices in the doubled physical layout -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix
open scoped Matrix
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The fixed Walsh stage on the half selector, leaving the frequency unchanged. -/
def physicalHalfWalsh : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  halfWalsh.submatrix dilationAddress dilationAddress

/-- Each of the three phase stages looks up one of two explicit entries
according to the half selector. -/
def physicalDilationPhase (z : ι → ℂ) (i j : Fin 6) : ι ⊕ ι → ℂ :=
  dilationPhase z i j ∘ dilationAddress

omit [Fintype ι] [DecidableEq ι] in
theorem physicalDilationPhase_norm (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1/2)
    (i j : Fin 6) (x : ι ⊕ ι) : ‖physicalDilationPhase z i j x‖ = 1 :=
  dilationPhase_norm z hz i j _

theorem physical_dilation (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1/2) :
    dilation z = physicalHalfWalsh * diagonal (physicalDilationPhase z 0 1) *
      physicalHalfWalsh * diagonal (physicalDilationPhase z 2 3) *
      physicalHalfWalsh * diagonal (physicalDilationPhase z 4 5) := by
  let t := @dilationAddress ι
  have h := congrArg (reindexRingEquiv ℂ t.symm) (dilation_explicit_threeWalsh z hz)
  simp only [map_mul] at h
  have hleft : reindexRingEquiv ℂ t.symm ((dilation z).submatrix t.symm t.symm) = dilation z := by
    ext x y
    change dilation z (t.symm (t x)) (t.symm (t y)) = _
    simp
  rw [hleft] at h
  have hd (i j : Fin 6) : reindexRingEquiv ℂ t.symm (diagonal (dilationPhase z i j)) =
      diagonal (physicalDilationPhase z i j) :=
    submatrix_diagonal_equiv _ t
  rw [hd, hd, hd] at h
  exact h

end
end ShortFourier

end NearSquareRoot
end Computability
end OAI
