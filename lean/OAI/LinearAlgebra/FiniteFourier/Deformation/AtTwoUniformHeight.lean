import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformation

/-! # Recovery with a common jet height

In a family of blocks with different numbers of active axes, the same long jet can be
used for all the blocks whenever it dominates each block's recovery threshold.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

variable {R : Type*} [CommRing R]

/-- Recover the integral product at one using any sufficiently long jet at zero. -/
theorem recover_integral_multiply_of_le {σ : Type*} [Fintype σ] [DecidableEq σ]
    (r H : ℕ) (hr : 0 < r) (hH : 2 * r + 2 * Fintype.card σ ≤ H)
    (ρ β : σ → R) (m : σ → ℕ) (x y : (∀ i, Fin 2 × Fin (m i)) → Jet R r) (k) :
    let input := specialize (0 : R) H ∘ liftJet 1 r
    readAtOne H r (multiply (fun a b c => specialize 0 H (integralCoeff ρ β m a b c))
        (input ∘ x) (input ∘ y) k) =
      multiply (fun a b c => specialize 1 r (integralCoeff ρ β m a b c)) x y k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [Nat.add_assoc]
  exact
    recover_multiply r (2 * Fintype.card σ + d) hr (integralCoeff ρ β m)
      (fun a b c => (natDegree_integralCoeff ρ β m a b c).trans (Nat.le_add_right ..)) x y k

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
