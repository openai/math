import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeAxis
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeWordMatrix
import OAI.LinearAlgebra.FiniteFourier.DyadicPrimeWordReindex

/-! # The Rader matrix in the binomial deformation basis -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.DyadicPrimeAxis

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
    {C : PrimeAxisOrbit p} {u : Rˣ} {hm : IsUnit ((p-1 : ℕ) : R)} (a : DyadicPrimeAxis R p C u hm)

/-- In the multiplicative orbit order the algebra map has the matrix synthesized by
the Fourier word, unit diagonal and two-channel zero-frequency mixer. -/
theorem forward_submatrix :
    a.forward.submatrix id C.optionEquiv =
      dyadicPrimeForwardMatrix ⟨0, by have := (Fact.out : p.Prime).two_le; omega⟩ u hm a.diagonal := by
  ext (k | k) (t | t) <;> simp [Matrix.submatrix_apply, dyadicPrimeForwardMatrix,
    forward_some_orbit, forward_some_zero]

end Deformation.DyadicPrimeAxis

end FiniteFourier
end LinearAlgebra
end OAI
