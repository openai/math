import OAI.LinearAlgebra.SpectralBooks.ContractionPrice

/-! # Detecting a nonzero tensor by contraction at the new party -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators

namespace SiteTensor.Raw

universe v
variable {I K : Type*} [Fintype I] [Field K]

/-- Contracting against a coordinate covector recovers a nonzero slice of
any nonzero enlarged tensor. -/
theorem exists_contractNew_ne_zero (T : Raw.{v} (Option I) K) (h : T.coeff ≠ 0) :
    ∃ ξ : T.Leg none → K, (T.contractNew ξ).coeff ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, T.coeff a ≠ 0 := by
    by_contra! hz
    exact h (funext hz)
  let e := Equiv.piOptionEquivProd (β := T.Leg)
  refine ⟨fun b ↦ if (e a).1 = b then 1 else 0, fun hz ↦ ha ?_⟩
  have hs := congrFun hz (e a).2
  change (∑ b, (if (e a).1 = b then 1 else 0) * T.coeff (e.symm (b, (e a).2))) = 0 at hs
  simpa [ite_mul] using hs

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
