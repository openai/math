import OAI.LinearAlgebra.SpectralBooks.SiteTensor.SumDef

/-! # Padding the local coordinate spaces with zeros -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical

namespace SiteTensor

open Crossing

variable {I K : Type*} [Fintype I] [CommSemiring K]
variable {A B : I → Type*} [∀ i, Fintype (A i)]

/-- Pushing the coefficients along local functions is a restriction, with each
basis vector sent to the basis vector indexed by its image. -/
theorem pushCoeff_restricts (f : ∀ i, A i → B i) (X : (∀ i, A i) → K) :
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨fun i b a => if f i a = b then 1 else 0, fun x => ?_⟩
  simp only [pushCoeff, Fintype.prod_boole, ← funext_iff, mul_ite, mul_one, mul_zero]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

/-- An injection of basis indices at each site pads a tensor with zeros.
The coordinate projections restrict the padded tensor back to the original. -/
theorem equivalent_pushCoeff [∀ i, Fintype (B i)] (f : ∀ i, A i ↪ B i)
    (X : (∀ i, A i) → K) :
    IsRestriction X (pushCoeff (fun x i => f i (x i)) X) ∧
    IsRestriction (pushCoeff (fun x i => f i (x i)) X) X := by
  refine ⟨?_, pushCoeff_restricts (fun i => f i) X⟩
  refine ⟨fun i a b => if b = f i a then 1 else 0, fun x => ?_⟩
  rw [sum_pushCoeff_mul]
  simp [Fintype.prod_boole, ← funext_iff, mul_ite]

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
