import OAI.LinearAlgebra.SpectralBooks.PowerSpan
import OAI.LinearAlgebra.SpectralBooks.TensorSemiring

/-! # Tensor powers in a fixed coordinate representation

Grouping the `n` copies of each local leg identifies a coordinate tensor
power with the `n`th power in the tensor semiring of finite-site tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

universe v

variable {I K : Type*} [Fintype I] [Nonempty I] [Field K]
  {A : I → Type v} [∀ i, Fintype (A i)]

/-- Group the `n` coordinates of each site into one local leg. -/
def groupedPower (n : ℕ) (T : (∀ i, A i) → K) (x : ∀ i, Fin n → A i) : K :=
  coordinatePower n T (fun j i ↦ x i j)

/-- The value of the grouped tensor power in the tensor semiring. -/
theorem ofRaw_groupedPower (n : ℕ) (T : (∀ i, A i) → K) :
    ofRaw (I := I) (K := K) ⟨fun i ↦ Fin n → A i, fun _ ↦ inferInstance, groupedPower n T⟩ =
      ofRaw (⟨A, inferInstance, T⟩ : Raw I K) ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ Equiv.equivPUnit (Fin 0 → A i))
    intro x
    change ∏ j : Fin 0, T (fun i ↦ x i j) = 1
    simp
  | succ n ih =>
    rw [pow_succ', ← ih, ← ofRaw_mul]
    apply Quotient.sound
    apply Raw.reindex_equivalent (fun i ↦ (Fin.consEquiv (fun _ : Fin (n + 1) ↦ A i)).symm)
    intro x
    exact Fin.prod_univ_succ (fun j ↦ T (fun i ↦ x i j))

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
