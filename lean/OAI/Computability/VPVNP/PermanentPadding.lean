import OAI.Computability.VPVNP.Circuits
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# Diagonal padding for the permanent

Section 15.1 of *VP and VNP differ over every field* pads a matrix of
indeterminates by adjoining one diagonal entry equal to one and setting all
other entries in its new row and column to zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

open Equiv MvPolynomial

/-- The permanent of the generic `m` by `m` matrix. -/
noncomputable def permanentPolynomial (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin m × Fin m) R :=
  Matrix.permanent (Matrix.of fun i j => X (i, j))

/-- The row-first formula used in the paper. -/
theorem permanentPolynomial_eq_sum (R : Type*) [CommSemiring R] (m : ℕ) :
    permanentPolynomial R m = ∑ π : Perm (Fin m), ∏ i, X (i, π i) := by
  exact (Matrix.permanent_transpose (Matrix.of fun i j : Fin m => X (R := R) (i, j))).symm

/-- Vertex zero is the new vertex, and `Fin.succ` embeds the old indices. -/
def permanentPadding (R : Type*) [CommRing R] (m : ℕ) :
    Projection R (Fin (m + 1) × Fin (m + 1)) (Fin m × Fin m) := fun (i, j) =>
  Fin.cases (Fin.cases (.inr 1) (fun _ => .inr 0) j)
    (fun i => Fin.cases (.inr 0) (fun j => .inl (i, j)) j) i

/-- Exactly the permutations fixing the new index survive diagonal padding. -/
theorem permanentPadding_polynomial (R : Type*) [CommRing R] (m : ℕ) :
    (permanentPadding R m).hom (permanentPolynomial R (m + 1)) = permanentPolynomial R m := by
  classical
  rw [permanentPolynomial_eq_sum, permanentPolynomial_eq_sum, map_sum,
    Finset.univ_perm_fin_succ, Finset.sum_map, Fintype.sum_prod_type, Fin.sum_univ_succ]
  simp only [Equiv.toEmbedding_apply, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ]
  simp [Projection.hom, permanentPadding]

end VPVNP
end Computability
end OAI
