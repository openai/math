import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Restriction

/-! # Absorbing a scalar in one tensor leg -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

variable {I K : Type*} [Fintype I] [Nonempty I] [CommSemiring K]
  {A : I → Type*} [∀ i, Fintype (A i)]

/-- Scaling the identity matrix at one site realizes a scalar multiple as a
restriction. The scalar may be zero. -/
theorem scalar_mul_restricts (c : K) (T : (∀ i, A i) → K) :
    Crossing.IsRestriction (c • T) T := by
  classical
  let i₀ := Classical.arbitrary I
  refine ⟨fun i y x ↦ if x = y then (if i = i₀ then c else 1) else 0, fun x ↦ ?_⟩
  simp_rw [Fintype.prod_ite_zero]
  simp [← funext_iff, mul_ite, mul_comm]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
