import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteLabelCost
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumQueries
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectralCost

/-! # Fourier batch obtained from the compiled Hermite repair

The same corrected multiplier acts on every label, and removing its quadratic
input and output phases recovers the ordinary prime transform on every row.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
open scoped Classical

variable {K : Type*} [CommRing K] {ℓ : ℕ} [NeZero ℓ] [Invertible (ℓ : K)]
variable {C J U L : Type} [Fintype C] [Fintype J] [Fintype U] [Fintype L]

local notation "Digits" => PrimeSpectrumDigits (C × (J ⊕ U)) ℓ

/-- A compiled and correct pencil stage supplies a batch of ordinary prime
Fourier transforms. Its call coefficient includes both directions of the
spectral table and all powers of the shared pencil. -/
theorem realizableAtMost_primeTransform_of_hermiteRepair
    {W s b A f localCoeff stageCalls : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ]
    (hm : Fintype.card J ≡ 1 [MOD ℓ]) (hsize : 2 * Fintype.card (C × (J ⊕ U)) = A*f)
    (u : K) (P : (Fin W → L × Digits → K) → Fin W → L × Digits → K)
    (H : Matrix (Fin s) (Fin W) K)
    (T : L × Digits → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)))
    (hP : RealizesRows P (localCoeff * Fintype.card Digits +
      stageCalls * ℓ ^ ((A-1)*f) * complexity (primeTransform ℓ f ζ)))
    (hrepair : let S := primeLabelSpectralEquiv L (primeSpectrumEquiv (ι := C × (J ⊕ U)) hζ)
      ∀ x w, hermiteRepairProgram ℓ u (P^[b]) S H T x w =
        S.symm ((fun p : L × Digits =>
          ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry p.2.1) (Function.curry p.2.2) j) *
            S (x w))) :
    RealizableAtMost
      (Matrix.blockDiagonal (fun _ : Fin (Fintype.card L * W) => primeTransform ℓ (A*f) ζ))
      ((((ℓ+2)*b)*localCoeff + hermiteLocalCost W s * Fintype.card L) * ℓ ^ (A*f) +
        (((ℓ+2)*b)*stageCalls + 4*s*Fintype.card L*A) * ℓ ^ ((A-1)*f) * complexity (primeTransform ℓ f ζ)) := by
  let S := primeSpectrumEquiv (ι := C × (J ⊕ U)) hζ
  let z (ω : Digits) := ∏ j, primeQueryMultiplier (digitPhase hζ) (Function.curry ω.1) (Function.curry ω.2) j
  let M := Matrix.of (fun o i : Digits => primeTupleKernelRing hζ i.1 i.2 o.1 o.2)
  have hM : ∀ x, S.symm (z * S x) = M.mulVec x := by
    intro x
    change (primeSpectrumMultiplier hζ z) x = M.mulVec x
    have he : (primeSpectrumMultiplier hζ z).toMatrix' = M := primeSpectrumQueryProduct_matrix hζ hm
    rw [← he, LinearMap.toMatrix'_mulVec]
  have hf : RealizesOp S (A * ℓ ^ ((A-1)*f) * complexity (primeTransform ℓ f ζ)) := RealizesOp.of_toMatrix' S.toLinearMap (by
    have hs := (primeTemplate_spectral_forward hζ hsize).compile
    rw [zero_add] at hs
    convert! hs using 1)
  have hi : RealizesOp S.symm (A * ℓ ^ ((A-1)*f) * complexity (primeTransform ℓ f ζ)) := RealizesOp.of_toMatrix' S.symm.toLinearMap (by
    have hs := (primeTemplate_spectral_inverse hζ hsize).compile
    rw [zero_add] at hs
    convert! hs using 1)
  have hk := realizableAtMost_hermiteLabelBatch u P S H T z M rfl hP hf hi hrepair hM
  have hvol : Fintype.card Digits = ℓ ^ (A*f) := by
    simp only [PrimeSpectrumDigits, Fintype.card_prod, Fintype.card_fun, ZMod.card, ← pow_add]
    rw [← hsize]
    congr 1
    simp [two_mul]
  rw [hvol] at hk
  exact realizableAtMost_batchedTupleKernel hζ hsize hk

end

end

end FiniteFourier
end LinearAlgebra
end OAI
