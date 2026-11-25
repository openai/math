import OAI.LinearAlgebra.FiniteFourier.Upper
import OAI.LinearAlgebra.FiniteFourier.MonomialLayer
import OAI.LinearAlgebra.FiniteFourier.ShearDescent
import OAI.LinearAlgebra.FiniteFourier.ShearLayerCost

/-! # Word costs over protected coefficient rings

Each monomial stage uses one fixed ring multiplication per spatial address.
Each shear stage acts on every basis coordinate with the same integral matrix.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R J : Type*} [CommRing R] [CommRing J] [Algebra R J]
    {I : Type} [Fintype I] [DecidableEq I] {D : Type*} [Fintype D] [DecidableEq D]

/-- Restrict all stages in one word to base-ring coordinates. This applies to
both truncated jet rings, including their nilpotent coefficients. -/
theorem LayerWord.realizable_restrict_of_shear_bound {A : Matrix I I J} {d s : ℕ}
    {β C : ℝ} (hw : LayerWord d A) (b : Module.Basis D R J)
    (hc : ∀ u : Jˣ, RealizableAtMost (fun i j : D => b.repr ((u : J)*b j) i) s)
    (ht : ShearTensorBound R β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    RealizableAtMost (restrictMatrix b A) (d*(Fintype.card I*s +
      Fintype.card D*⌊C*(Fintype.card I : ℝ)*(1+Real.logb 2 (Fintype.card I))^β⌋₊)) :=
  realizable_restrictMatrix_of_word b hw
    (fun _ h => h.restrictMatrix_monomial_uniform b hc)
    (fun _ h => realizable_restrict_shear b h (fun _ hb => ht.realizable_layer hC hβ hb))

end FiniteFourier
end LinearAlgebra
end OAI
