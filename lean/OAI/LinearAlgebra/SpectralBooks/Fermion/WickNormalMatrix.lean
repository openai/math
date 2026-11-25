import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFields
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickHomogeneous
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickFinite

/-! # Stabilization of normal products on finite Fock spaces -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace Fermion

open Finset LaurentPolynomial

private theorem sum_fock_modes {N : ℕ} (S : FockState N) (g : ℕ → LaurentPolynomial ℤ) :
    (∑ r : Fin N, if r.val ∈ S.val then g r.val else 0) = ∑ r ∈ S.val, g r := by
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ ↦ if r ∈ S.val then g r else 0), ← Finset.sum_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (inter_eq_right.mpr (mem_powerset.mp S.property))

/-- Every finite normal-product matrix element agrees with its unrestricted Laurent polynomial.
This holds for every cutoff containing its input and output, including residual words in
the two expansion orders. -/
theorem normal_matrix_apply (N : ℕ) (l : List FieldLabel) (α β : FockState N) :
    normal (LaurentPolynomial ℤ)
      (creationField N) (annihilationField N)
      l α β = mixedNormal l α.val β.val := by
  change normal (LaurentPolynomial ℤ)
    (fun f ↦ ∑ r : Fin N, creationCoeff f r • creation (LaurentPolynomial ℤ) r)
    (fun f ↦ ∑ r : Fin N, annihilationCoeff f r • annihilation (LaurentPolynomial ℤ) r)
    l α β = _
  induction l generalizing α β with
  | nil => simp only [normal, mixedNormal, Matrix.one_apply, Subtype.ext_iff]
  | cons f l ih =>
    simp only [normal, mixedNormal, Finset.sum_mul, Finset.mul_sum,
      smul_mul_assoc, mul_smul_comm,
      Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      creation_mul_apply, mul_annihilation_apply, mul_ite, mul_zero, ih, FockState.erase]
    rw [← sum_fock_modes α, ← sum_fock_modes β]
    congr 1
    · apply sum_congr rfl
      intro r _
      simp [mul_assoc]
    · apply sum_congr rfl
      intro r _
      simp [mul_left_comm, mul_comm]

/-- The increasing word of divided derivatives for a single block at one variable. -/
def fieldWord (side : Bool) (I : State) : List FieldLabel :=
  (I.sort (· ≤ ·)).map (Prod.mk side)

/-- The matrix of a normal block in the cutoff Fock space. -/
def fieldMatrix (N : ℕ) (side : Bool) (I : State) :
    Matrix (FockState N) (FockState N) (LaurentPolynomial ℤ) :=
  normal (LaurentPolynomial ℤ) (creationField N) (annihilationField N) (fieldWord side I)

/-- The cutoff matrix of a pure block has exactly the mode coefficient in its possible
degree. On setting the first variable to one this becomes a constant Laurent polynomial. -/
theorem fieldMatrix_apply (N : ℕ) (side : Bool) (I : State) (α β : FockState N) :
    fieldMatrix N side I α β =
      C (blockMode I (modeDegree (I.sort (· ≤ ·)) α.val β.val) α.val β.val) *
        T (fieldExponent side (modeDegree (I.sort (· ≤ ·)) α.val β.val)) := by
  rw [fieldMatrix, normal_matrix_apply, fieldWord, mixedNormal_one_variable]
  rfl

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
