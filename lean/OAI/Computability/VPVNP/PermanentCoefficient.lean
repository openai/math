import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent

/-!
# The permanent as a squarefree column coefficient

In a product of row forms, a summand chooses one column in each row. It contributes
to the monomial using every column once precisely when the choices form a permutation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PermanentReduction

open MvPolynomial
open scoped BigOperators

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]

/-- One occurrence of each column. -/
noncomputable def fullDegree (V : Type*) [Fintype V] : V →₀ ℕ :=
  ∑ j : V, Finsupp.single j 1

@[simp] theorem fullDegree_apply (j : V) : fullDegree V j = 1 := by
  simp [fullDegree, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem degrees_eq_full_iff (f : V → V) :
    (∑ i, Finsupp.single (f i) 1) = fullDegree V ↔ Function.Bijective f := by
  constructor
  · intro h
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    refine ⟨?_, rfl⟩
    intro j
    by_contra! hmiss
    have hj := DFunLike.congr_fun h j
    simp [Finsupp.finsetSum_apply, hmiss] at hj
  · intro hf
    exact (Equiv.ofBijective f hf).sum_comp (fun j => Finsupp.single j 1)

omit [Fintype V] [DecidableEq V] in
theorem prod_monomials {I : Type*} (s : Finset I) (d : I → V →₀ ℕ) (a : I → R) :
    (∏ i ∈ s, monomial (d i) (a i)) = monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The product of the row forms over an arbitrary finite index type. -/
noncomputable def rowProduct (M : Matrix V V R) : MvPolynomial V R :=
  ∏ i, ∑ j, C (M i j) * X j

theorem coeff_rowProduct (M : Matrix V V R) : (rowProduct M).coeff (fullDegree V) = M.permanent := by
  classical
  simp only [rowProduct, Fintype.prod_sum, C_mul_X_eq_monomial, prod_monomials, coeff_sum,
    coeff_monomial, degrees_eq_full_iff]
  rw [← Finset.sum_filter]
  have hsub := Finset.sum_subtype (p := Function.Bijective (α := V) (β := V))
    (F := inferInstance)
    (Finset.univ.filter Function.Bijective) (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x)))
    (fun f : V → V => ∏ i, M i (f i))
  rw [hsub]
  calc
    _ = ∑ e : Equiv.Perm V, ∏ i, M i (e i) :=
      Equiv.bijectiveEquiv.sum_comp (fun e : Equiv.Perm V => ∏ i, M i (e i))
    _ = M.permanent := Matrix.permanent_transpose M

end PermanentReduction

end VPVNP
end Computability
end OAI
