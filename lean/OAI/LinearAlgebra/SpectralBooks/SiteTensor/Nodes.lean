import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Split
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Placed tensors in the two-endpoint coupling proof

A wire split keeps the first mark free and appends an exterior column and row
at fixed sites. Keeping the other free index among the background legs allows
one tensor to be evaluated at all four choices of the two endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace SiteTensor.Relocation

/-- A nonzero node of the binary-wire splitting argument. Both marks can
be moved independently. The offset is the cost of exterior wires added by
earlier splits. -/
structure WireNode (K : Type*) [Field K] (J : Type) (Q : ℕ) where
  I : Type
  [finiteI : Fintype I]
  A : I → Type
  [finiteA : ∀ i, Fintype (A i)]
  other : I
  site : I → J
  T : (∀ i, A i) → Fin Q → K
  nonzero : (marked A (Fin Q) T).coeff ≠ 0
  offset : ℝ

attribute [instance] WireNode.finiteI WireNode.finiteA

namespace WireNode

variable {K : Type*} [Field K] {J : Type} [Fintype J] [Nonempty J] {Q : ℕ}

def cost (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)
    (N : WireNode K J Q) (p v : J) : ℝ :=
  rawLogPrice φ c ((marked N.A (Fin Q) N.T).group
    (placeMark (Function.update N.site N.other v) p)) - N.offset

end WireNode
end SiteTensor.Relocation

end

end SpectralBooks
end LinearAlgebra
end OAI
