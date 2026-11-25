import OAI.LinearAlgebra.FiniteFourier.PrimeFixedRepair
import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleSystem
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumRepair

/-! # Parameters and ordinary stages of the repaired Fourier batch -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

/-- The two halves of the row, consisting of distinguished and auxiliary digits. -/
abbrev primeRowDigits (ℓ m D f : ℕ) :=
  PrimeSpectrumDigits (Fin f × (Fin m ⊕ Fin (D-1))) ℓ

/-- The per-stage budget: transforms at each free incidence and one common
transform for each charged rectangle and distinguished digit. -/
def primePencilCalls (ℓ L v m D R : ℕ) : ℕ :=
  (2*ℓ*D*R) * (2*(2^v)^L*(1+v)^L + m*(2^L*(2^v)^(L/ℓ)))

variable {K : Type*} [CommRing K] {ℓ m b L v f D : ℕ} [NeZero ℓ] [Invertible (ℓ : K)]
  {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]

/-- Each query acts on its own distinguished digit and all auxiliary digits
independently at every label. -/
def primeBatchQuery (L v m D f : ℕ) (j : Fin m) :
    Module.End K (BitLabel L v × primeRowDigits ℓ m D f → K) :=
  primeLabelMap fun _ => primeSpectrumQuery hζ (fun ω =>
    primeQueryExponent (Function.curry ω.1) (Function.curry ω.2) j)

/-- The ordinary predictor stage on the full label array. -/
def primeConcreteStage (S : PrimeRectangleSystem K ℓ L v)
    (p : PrimeRepairPencil ℓ m b hζ) (f : ℕ) :
    (Fin (primePredictorRows ℓ m b) → BitLabel L v × primeRowDigits ℓ m S.D f → K) →
      (Fin (primePredictorRows ℓ m b) → BitLabel L v × primeRowDigits ℓ m S.D f → K) :=
  queryPencilStage (primeBatchQuery hζ L v m S.D f) p.A₀ p.A

theorem primeBatchQuery_spectral (j : Fin m)
    (x : BitLabel L v × primeRowDigits ℓ m D f → K) (ω : BitLabel L v × primeRowDigits ℓ m D f) :
    primeLabelSpectralEquiv _ (primeSpectrumEquiv hζ) (primeBatchQuery hζ L v m D f j x) ω =
      digitPhase hζ (primeQueryExponent (Function.curry ω.2.1) (Function.curry ω.2.2) j) *
        primeLabelSpectralEquiv _ (primeSpectrumEquiv hζ) x ω :=
  primeSpectrumEquiv_query hζ _ (fun a => x (ω.1,a)) ω.2

end

end

end FiniteFourier
end LinearAlgebra
end OAI
