import OAI.LinearAlgebra.FiniteFourier.PrimeCommonChartAgreement
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonQuery

/-! # The physical transfer of the ordinary query powers -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {ℓ m : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
variable {C U E : Type*} [Fintype C] [Fintype U] [AddCommGroup E] [Module (ZMod ℓ) E]

/-- The common transfer in the uniformly numbered physical chart is precisely
the ordinary operator for this query power. Both the common space and its
spectator addresses are independent of the selected distinguished slot. -/
theorem primeCommonKernel_physical_queryPower (hζ : IsPrimitiveRoot ζ ℓ)
    [PrimeSpectrumOrthogonal hζ] (B : E →ₗ[ZMod ℓ] E →ₗ[ZMod ℓ] ZMod ℓ)
    (p q : E ≃ₗ[ZMod ℓ] ZMod ℓ × (U → ZMod ℓ))
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ u, (p x).2 u * (q y).2 u)
    (j : Fin (m+1)) (a : (ZMod ℓ)ˣ) :
    let physical := endpointDigitCurry.trans (endpointQueryPhysicalChart (C := C) j p.toEquiv q.toEquiv)
    (primeCommonKernel hζ B a (Fintype.card (Unit ⊕ U))).submatrix physical physical =
      ((primeSpectrumQuery hζ (fun ω => primeCommonQueryExponents ω j)) ^ (a : ZMod ℓ).val).toMatrix' := by
  dsimp only
  rw [primeCommonKernel_physical hζ B a (Fintype.card (Unit ⊕ U)) j p q]
  exact primeCommonKernel_eq_queryPower hζ B _ _ (primeCommonLabelMap_pair B p q hpq) j a

end

end

end FiniteFourier
end LinearAlgebra
end OAI
