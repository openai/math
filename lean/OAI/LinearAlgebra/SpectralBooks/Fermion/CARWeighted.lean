import OAI.LinearAlgebra.SpectralBooks.Fermion.WickOrder

/-! # Fermionic anticommutation for finite superpositions of modes

A finite linear combination of creation or deletion modes preserves the
anticommutation rules by bilinearity. The mixed contraction is the scalar
dot product of the two coefficient families.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Finset

variable {k E ι : Type*} [CommRing k] [Ring E] [Algebra k E] [Fintype ι]

/-- Bilinearity of the anticommutator over a finite set of modes. -/
private theorem weighted_anticommutator (a c : ι → E) (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • c j) + (∑ j, w j • c j) * (∑ i, v i • a i) =
      ∑ i, ∑ j, (v i * w j) • (a i * c j + c j * a i) := by
  simp only [sum_mul, mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul, smul_add]
  rw [Finset.sum_comm (f := fun j i ↦ (w j * v i) • (a i * c j)),
    ← Finset.sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ by simp [Finset.sum_add_distrib, mul_comm]

/-- Two linear combinations of mutually anticommuting modes anticommute. -/
theorem weighted_same_modes (a : ι → E) (h : ∀ i j, a i * a j + a j * a i = 0)
    (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • a j) + (∑ j, w j • a j) * (∑ i, v i • a i) = 0 := by
  rw [weighted_anticommutator]
  simp [h]

/-- The mixed creation–deletion contraction is the scalar pairing of the coefficients. -/
theorem weighted_mixed_modes [DecidableEq ι] (a c : ι → E)
    (h : ∀ i j, a i * c j + c j * a i = if i = j then 1 else 0) (v w : ι → k) :
    (∑ i, v i • a i) * (∑ j, w j • c j) + (∑ j, w j • c j) * (∑ i, v i • a i) =
      algebraMap k E (∑ i, v i * w i) := by
  rw [weighted_anticommutator]
  simp [h, smul_ite, Algebra.algebraMap_eq_smul_one]

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
