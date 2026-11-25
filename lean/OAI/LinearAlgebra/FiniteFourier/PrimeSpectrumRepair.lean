import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumQueries
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteLabel
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowRepair

/-! # Ordinary readout of the paired Fourier product after repair -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section

section

open scoped Classical

variable {K C U : Type*} [CommRing K] [Fintype C] [Fintype U] {ℓ m : ℕ}
  [NeZero ℓ] [Invertible (ℓ : K)] {ζ : K}

/-- Converting the repaired multiplier back to ordinary coordinates applies
the full dot-product kernel to the input. -/
theorem primeSpectrum_repairReadout (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hm : m ≡ 1 [MOD ℓ]) (v : PrimeSpectrumDigits (C × (Fin m ⊕ U)) ℓ → K) :
    (primeSpectrumEquiv hζ).symm
      ((fun ω => countQueryProduct hζ (primeQueryExponent (Function.curry ω.1) (Function.curry ω.2))) *
        primeSpectrumEquiv hζ v) =
      (Matrix.of fun s x => primeTupleKernelRing hζ x.1 x.2 s.1 s.2).mulVec v := by
  let f (ω : PrimeSpectrumDigits (C × (Fin m ⊕ U)) ℓ) :=
    countQueryProduct hζ (primeQueryExponent (Function.curry ω.1) (Function.curry ω.2))
  have hM := primeSpectrumQueryProduct_matrix (C := C) (J := Fin m) (U := U) hζ (by simpa using hm)
  exact (LinearMap.toMatrix'_mulVec (primeSpectrumMultiplier hζ f) v).symm.trans
    (congrArg (fun M => Matrix.mulVec M v) hM)

/-- At every independent rectangle label, Hermite repair reads out the same
ordinary quadratic kernel on that label's row of input digits. -/
theorem primeSpectrum_labelRepairReadout {L : Type*} (hζ : IsPrimitiveRoot ζ ℓ)
    [PrimeSpectrumOrthogonal hζ] (hm : m ≡ 1 [MOD ℓ])
    (v : L × PrimeSpectrumDigits (C × (Fin m ⊕ U)) ℓ → K) :
    (primeLabelSpectralEquiv L (primeSpectrumEquiv hζ)).symm
      ((fun ω => countQueryProduct hζ
        (primeQueryExponent (Function.curry ω.2.1) (Function.curry ω.2.2))) *
        primeLabelSpectralEquiv L (primeSpectrumEquiv hζ) v) =
      fun p => (Matrix.of fun s x => primeTupleKernelRing hζ x.1 x.2 s.1 s.2).mulVec
        (fun a => v (p.1, a)) p.2 := by
  funext p
  exact congrFun (primeSpectrum_repairReadout hζ hm (fun a => v (p.1, a))) p.2

end

end

end FiniteFourier
end LinearAlgebra
end OAI
