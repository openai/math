import OAI.LinearAlgebra.FiniteFourier.PrimeAffineStage
import OAI.LinearAlgebra.FiniteFourier.PrimeOrdinaryPencil
import OAI.LinearAlgebra.FiniteFourier.PrimeWindowRepair

/-! # Repair with ordinary query-pencil stages

Actual powers of the queries act on mixing matrices in ordinary coordinates.
After the stages for the shifted-count predictor, a two-block spectral table
repairs every row of the full batch.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

/-- A product of diagonalizable query operators can be applied to all independent
batch inputs by the ordinary query-pencil construction and Hermite repair.
The coefficient field contains the indicated primitive roots. A check-node
injection is needed only after the common clock-block width has been chosen. -/
theorem exists_correct_queryPencilRepair {K V ν : Type*} [Field K] [AddCommGroup V] [Module K V]
    {ℓ m b : ℕ} [NeZero ℓ] [NeZero b] {ζ ξ : K}
    (hℓ : 2 ≤ ℓ) (hm : 2 ≤ m) (hζ : IsPrimitiveRoot ζ ℓ) (hξ : IsPrimitiveRoot ξ b)
    (hD : repairWindowDegree ℓ m ≤ b) (S : V ≃ₗ[K] (ν → K)) (k : ν → Fin m → ZMod ℓ)
    (Q : Fin m → Module.End K V)
    (hQ : ∀ j x ω, S (Q j x) ω = digitPhase hζ (k ω j) * S x ω) :
    ∃ (h : ℕ) (A₀ : (Fin m → ZMod ℓ) → Matrix (Fin h → Fin b) (Fin h → Fin b) K)
      (A : (Fin m → ZMod ℓ) → Fin m → ZMod ℓ → Matrix (Fin h → Fin b) (Fin h → Fin b) K),
      ∀ ρ : Fin (ℓ ^ m * b ^ h) → K, Function.Injective ρ →
        let s := countRepairChecks ℓ m (b ^ h)
        ∃ T : ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)),
          ∀ x i, hermiteRepairProgram ℓ (ℓ : K)⁻¹ (queryPencilStage Q A₀ A)^[b]
            S (repairCheck ρ s) T x i = S.symm ((fun ω => countQueryProduct hζ (k ω)) * S (x i)) := by
  obtain ⟨h, L, haff, _, hrepair⟩ := exists_correct_countPencilRepair hℓ hm hζ hξ hD S k
  choose A₀ A hc using fun β => exists_queryPencil_coefficients hζ (L β) (haff β)
  refine ⟨h, A₀, A, ?_⟩
  rw [queryPencilStage_eq_countPencilStep Q A₀ A hζ S k hQ L hc]
  exact hrepair

end

end

end FiniteFourier
end LinearAlgebra
end OAI
