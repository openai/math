import OAI.Computability.NearSquareRoot.SynchronizedPadding
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.PEquiv

/-! # Composition of simultaneous layers on disjoint address blocks

Each layer applies one local matrix per block. Multiplying the full layers in order
performs the local matrix product independently on each block.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPadding

open Matrix Finset

variable {ι R : Type*} {A : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (A i)] [CommSemiring R]

theorem tensorMatrix_mul (U V : ∀ i, Matrix (A i) (A i) R) :
    tensorMatrix (fun i ↦ U i * V i) = tensorMatrix U * tensorMatrix V := by
  ext x y
  simp only [tensorMatrix, of_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp only [prod_mul_distrib]

variable [∀ i, DecidableEq (A i)]

omit [DecidableEq ι] [∀ i, Fintype (A i)] in
@[simp] theorem tensorMatrix_one :
    tensorMatrix (R := R) (fun i ↦ (1 : Matrix (A i) (A i) R)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [one_apply_ne h]
    apply prod_eq_zero (mem_univ i)
    exact one_apply_ne hi


omit [DecidableEq ι] [∀ i, Fintype (A i)] in
/-- The global phase stream is the product of the local table entries. -/
theorem tensorMatrix_diagonal (d : ∀ i, A i → R) :
    tensorMatrix (fun i ↦ diagonal (d i)) = diagonal (fun x ↦ ∏ i, d i (x i)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [tensorMatrix]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [diagonal_apply_ne _ h]
    apply prod_eq_zero (mem_univ i)
    exact diagonal_apply_ne _ hi

omit [DecidableEq ι] [∀ i, Fintype (A i)] in
/-- Simultaneous independent block permutations form the coordinatewise
permutation of all addresses. -/
theorem tensorMatrix_blockPerm (e : ∀ i, Equiv.Perm (A i)) :
    tensorMatrix (R := R) (fun i ↦ (e i).toPEquiv.toMatrix) =
      (Equiv.piCongrRight e).toPEquiv.toMatrix := by
  ext x y
  by_cases h : (Equiv.piCongrRight e) x = y
  · subst y
    simp [tensorMatrix, PEquiv.toMatrix_apply]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    change e i (x i) ≠ y i at hi
    rw [PEquiv.toMatrix_apply, ite_eq_right (by simpa using h)]
    apply prod_eq_zero (mem_univ i)
    change (e i).toPEquiv.toMatrix (α := R) (x i) (y i) = 0
    simp [PEquiv.toMatrix_apply, hi]

/-- The word is listed in matrix multiplication order, so its last matrix
acts first on the input. Local words can contain identity padding. -/
theorem tensorMatrix_list_prod (layers : List (∀ i, Matrix (A i) (A i) R)) :
    tensorMatrix (fun i ↦ (layers.map (fun layer ↦ layer i)).prod) =
      (layers.map tensorMatrix).prod := by
  induction layers with
  | nil => simp
  | cons layer layers ih =>
    simp only [List.map_cons, List.prod_cons, tensorMatrix_mul, ih]

end SynchronizedPadding

end NearSquareRoot
end Computability
end OAI
