import OAI.LinearAlgebra.FiniteFourier.PhasePrice

/-! # The four-leg tensor of a weighted swap

The extra basis coordinate at the center records the pair of output
labels. When these two labels have been copied there, a single local
functional changes all nonzero swap weights to one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor
open scoped Classical

variable {G : Type} {K : Type*} [Field K] [Fintype G]

/-- The four-leg coefficient of a weighted swap, with the weight indexed by
the pair of output labels as in the two-phase construction. -/
def weightedSwapEntry (w : G × G → K) (i j i' j' : G) : K :=
  if i = j' ∧ j = i' then w (i',j') else 0

/-- The corresponding two-register operator matrix. -/
def weightedSwapMatrix (w : G × G → K) : Matrix (G × G) (G × G) K :=
  fun y x ↦ weightedSwapEntry w x.1 x.2 y.1 y.2

/-- The four-site tensor of the weighted swap. -/
def swapRaw (w : G × G → K) : Raw (Fin 4) K := operatorRaw (weightedSwapMatrix w)

theorem swapRaw_coeff (w : G × G → K) (z : ∀ i, phaseLeg G G i) :
    (swapRaw w).coeff z = weightedSwapEntry w (z 0) (z 1) (z 2) (z 3) := rfl

end

end FiniteFourier
end LinearAlgebra
end OAI
