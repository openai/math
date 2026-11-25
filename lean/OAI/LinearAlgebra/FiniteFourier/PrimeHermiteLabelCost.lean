import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteCost
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteLabel
import OAI.LinearAlgebra.FiniteFourier.PrimeHermiteBatch

/-! # Cost of all independent outputs of a labeled query pencil -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K α ν L : Type*} [CommRing K] [Fintype α] [Fintype ν] [Fintype L]

/-- A correct repaired pencil gives the common matrix on every label and every
independent input. The first term counts the work local to an array coordinate.
The second charges all pencil stages and the four spectral conversions per check
row, in units of a single-axis transform over its fibers. -/
theorem realizableAtMost_hermiteLabelBatch
    {W s ℓ b C stageCalls axes fibers base : ℕ} (u : K)
    (P : (Fin W → L × α → K) → Fin W → L × α → K) (S : (α → K) ≃ₗ[K] (ν → K))
    (H : Matrix (Fin s) (Fin W) K)
    (T : L × ν → ((Fin s → K) × (Fin s → K)) →ₗ[K] ((Fin s → K) × (Fin s → K)))
    (z : ν → K) (M : Matrix α α K) (hcard : Fintype.card ν = Fintype.card α)
    (hP : RealizesRows P (C * Fintype.card α + stageCalls * fibers * base))
    (hf : RealizesOp S (axes * fibers * base))
    (hi : RealizesOp S.symm (axes * fibers * base))
    (hrepair : ∀ x w, hermiteRepairProgram ℓ u (P^[b]) (primeLabelSpectralEquiv L S)
      H T x w = (primeLabelSpectralEquiv L S).symm
        ((fun p : L × ν => z p.2) * primeLabelSpectralEquiv L S (x w)))
    (hM : ∀ x, S.symm (z * S x) = M.mulVec x) :
    RealizableAtMost (Matrix.blockDiagonal (fun _ : Fin (Fintype.card L * W) => M))
      ((((ℓ+2)*b)*C + hermiteLocalCost W s * Fintype.card L) * Fintype.card α +
        (((ℓ+2)*b)*stageCalls + 4*s*Fintype.card L*axes) * fibers * base) := by
  have h := realizesRows_hermiteRepairProgram (ℓ := ℓ) (b := b) u P
    (primeLabelSpectralEquiv L S) H T (by simp [hcard]) hP
    (realizesOp_primeLabelSpectralEquiv L S hf) (realizesOp_primeLabelSpectralEquiv_symm L S hi)
  have heq : hermiteRepairProgram ℓ u (P^[b]) (primeLabelSpectralEquiv L S) H T =
      fun (x : Fin W → L × α → K) w p => M.mulVec (fun i => x w (p.1, i)) p.2 := by
    funext x w p
    rw [hrepair]
    exact congrFun (hM (fun i => x w (p.1, i))) p.2
  rw [heq] at h
  convert h.uniformLabelBatch M using 1
  simp only [Fintype.card_prod]
  ring

end FiniteFourier
end LinearAlgebra
end OAI
