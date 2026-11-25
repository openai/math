import OAI.LinearAlgebra.FiniteFourier.PrimeBatchParameters
import OAI.LinearAlgebra.FiniteFourier.PrimeStrictSaving
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteTransform

/-! # The fixed Fourier batch from its ordinary pencil stage

One routed pencil at a time is compiled in ordinary coordinates. Applying it
to the same arrays through the full Hermite program produces independent Fourier
transforms at every label and clock row, with the prescribed call count.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {K : Type*} [CommRing K] {ℓ L v m : ℕ} [Fact ℓ.Prime]
  [Invertible (ℓ : K)] {ζ : K}

set_option maxHeartbeats 1200000 in
/-- A compiler for the one-stage routed predictor suffices for the entire
strictly-saving batch. Local gates and recursive calls have separate budgets. -/
theorem primeKernelBatch_of_compiledStage (S : PrimeRectangleSystem K ℓ L v)
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (p : PrimeRepairPencil ℓ m (countPencilOrder ℓ m) hζ)
    (ρ : Fin (primePredictorRows ℓ m (countPencilOrder ℓ m)) → K)
    (hρ : Pairwise fun i j => IsUnit (ρ i-ρ j)) (hm : 2 ≤ m) (hcong : m ≡ 1 [MOD ℓ])
    (hstage : ∃ C : ℕ, ∀ f : ℕ, 0 < f →
      RealizesRows (primeConcreteStage hζ S p f)
        (C * Fintype.card (primeRowDigits ℓ m S.D f) +
          primePencilCalls ℓ L v m S.D (primePredictorRows ℓ m (countPencilOrder ℓ m)) *
            ℓ^((2*(m+S.D-1)-1)*f) * complexity (primeTransform ℓ f ζ))) :
    ∃ C : ℕ, PrimeKernelBatch ℓ (2*(m+S.D-1)) ((2^v)^L * primePredictorRows ℓ m (countPencilOrder ℓ m))
      (primeKernelCallBudget ℓ L v m S.D (primePredictorRows ℓ m (countPencilOrder ℓ m))) C ζ := by
  let b := countPencilOrder ℓ m
  let W := primePredictorRows ℓ m b
  let s := countRepairChecks ℓ m (b ^ primeClockDigits ℓ m b)
  let labels := (2^v)^L
  let A := 2 * (m+S.D-1)
  obtain ⟨C,hC⟩ := hstage
  refine ⟨((ℓ+2)*b)*C + hermiteLocalCost W s * labels, fun f hf => ?_⟩
  let Y := primeRowDigits ℓ m S.D f
  let spec := primeSpectrumEquiv (ι := Fin f × (Fin m ⊕ Fin (S.D-1))) hζ
  let k : BitLabel L v × Y → Fin m → ZMod ℓ :=
    fun ω => primeQueryExponent (Function.curry ω.2.1) (Function.curry ω.2.2)
  obtain ⟨T,hT⟩ := p.correct (Fact.out : ℓ.Prime).two_le hm (⅟ (ℓ : K)) (invOf_mul_self _)
    ρ hρ (primeLabelSpectralEquiv (BitLabel L v) spec) k (primeBatchQuery hζ L v m S.D f)
    (fun j x ω => primeBatchQuery_spectral hζ j x ω)
  have hsize : 2 * Fintype.card (Fin f × (Fin m ⊕ Fin (S.D-1))) = A*f := by
    have hD := S.dimension_pos
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_sum, A]
    rw [show m+(S.D-1) = m+S.D-1 by omega]
    ring
  have h := realizableAtMost_primeTransform_of_hermiteRepair
    (C := Fin f) (J := Fin m) (U := Fin (S.D-1)) (L := BitLabel L v)
    (A := A) (f := f) (b := b) (W := W) (s := s) (localCoeff := C)
    (stageCalls := primePencilCalls ℓ L v m S.D W) hζ (by simpa only [Fintype.card_fin] using hcong) hsize (⅟ (ℓ : K))
    (primeConcreteStage hζ S p f) (repairCheck ρ s) T (by
      have h := hC f hf
      convert! h using 1
      all_goals congr! 5) hT
  have hl : Fintype.card (BitLabel L v) = labels := by simp [labels, BitLabel, BitLetter]
  rw [hl] at h
  have hcalls : ((ℓ+2)*b) * primePencilCalls ℓ L v m S.D W + 4*s*labels*A =
      primeKernelCallBudget ℓ L v m S.D W := by
    dsimp only [primeKernelCallBudget, primePencilCalls, countRepairChecks, W, s, b, labels, A, primePredictorRows]
    ring
  rw [← hcalls]
  exact h

end

end

end FiniteFourier
end LinearAlgebra
end OAI
