import OAI.Computability.BorderVNP.ResidueBoxIndex
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Coordinates of the finite test space

Each test coordinate consists of a ground-field basis element and an actual Laurent
monomial in the box of §10.2. A coefficient of (10.3) in this basis is one entry of
the matrix in (10.1). The matrix depends linearly on the scalar of the input monomial.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResiduePins

open ResidueBox Module Matrix
open scoped Matrix BigOperators Classical

variable {σ ι β E k : Type*} [Field E] [Field k] [Algebra k E] [Fintype σ] [Fintype ι] [Fintype β]

/-- The basis labels in (10.1), consisting of a constant basis label and a box exponent. -/
abbrev Index (β σ : Type*) (H : ℕ) := β × {e : Exponent σ // InBox H e}

/-- The test with a given basis scalar and monomial exponent. -/
noncomputable def test (B : Basis β k E) {H : ℕ} (i : Index β σ H) : Laurent σ E :=
  AddMonoidAlgebra.single i.2.val (B i.1)

/-- A supported Laurent polynomial is the sum of its single monomials over the finite box. -/
theorem sum_box_single (H : ℕ) (f : Laurent σ E)
    (hs : ∀ e ∈ f.coeff.support, InBox H e) :
    ∑ i : {e : Exponent σ // InBox H e}, AddMonoidAlgebra.single i.val (f.coeff i.val) = f := by
  classical
  apply AddMonoidAlgebra.coeffEquiv.injective
  ext e
  simp only [AddMonoidAlgebra.coeffEquiv_apply, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single]
  by_cases he : InBox H e
  · rw [Finset.sum_eq_single ⟨e, he⟩]
    · simp
    · intro j _ hne
      exact Finsupp.single_eq_of_ne (fun h => hne (Subtype.ext h.symm))
    · simp
  · have hz : f.coeff e = 0 := Finsupp.notMem_support_iff.mp (fun h => he (hs e h))
    rw [hz]
    apply Finset.sum_eq_zero
    intro j _
    exact Finsupp.single_eq_of_ne (fun h => he (h.symm ▸ j.property))

/-- The box-indexed pin vector of a linear functional. -/
noncomputable def pin (B : Basis β k E) (H : ℕ) (ℓ : Laurent σ E →ₗ[k] k) : Index β σ H → k :=
  fun i => ℓ (test B i)

/-- The dual pairing of the prime-field coordinates with the pin vector recovers the
functional on any Laurent polynomial supported in the box. -/
theorem coordinates_pair (B : Basis β k E) (H : ℕ) (ℓ : Laurent σ E →ₗ[k] k)
    (f : Laurent σ E) (hs : ∀ e ∈ f.coeff.support, InBox H e) :
    (∑ i : Index β σ H, B.repr (f.coeff i.2.val) i.1 * pin B H ℓ i) = ℓ f := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ e : {e : Exponent σ // InBox H e}, ℓ (AddMonoidAlgebra.single e.val (f.coeff e.val)) := by
      apply Finset.sum_congr rfl
      intro e _
      let L := ℓ.comp (AddMonoidAlgebra.lsingle (R := k) e.val)
      have h := congrArg L (B.sum_repr (f.coeff e.val))
      simpa only [map_sum, map_smul, smul_eq_mul, L, LinearMap.comp_apply,
        AddMonoidAlgebra.lsingle_apply, pin, test] using h
    _ = _ := by rw [← map_sum, sum_box_single H f hs]

/-- Prime-field-linear dependence of the entire matrix on the monomial scalar.
Each row is the coefficient vector of (10.3). -/
noncomputable def weights (B : Basis β k E) (H q : ℕ) (hq : 0 < q)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (μ : Exponent σ) :
    E →ₗ[k] Matrix (Index β σ H) (Index β σ H) k where
  toFun a i j := B.repr ((rowPolynomial q hq g root a (B i.1) i.2.val μ).coeff j.2.val) j.1
  map_add' a b := by
    ext i j
    simp only [rowPolynomial_coeff, add_mul, map_add, Finsupp.add_apply]
    rfl
  map_smul' r a := by
    ext i j
    simp only [rowPolynomial_coeff, smul_mul_assoc, map_smul, Finsupp.smul_apply]
    rfl

/-- Multiplication by the concrete coefficient matrix evaluates each transformed basis test. -/
theorem weights_mul_pin (B : Basis β k E) (L q : ℕ) (hq : 2 ≤ q)
    (g : ι → MvPolynomial (Option σ) E) (root : E →+* E) (a : E)
    (μ : Exponent σ) (hμt : μ none = 0) (hμ : ∀ i, 0 ≤ μ (some i) ∧ μ (some i) ≤ L)
    (ℓ : Laurent σ E →ₗ[k] k) :
    let H := radius L (∑ t, (g t).totalDegree)
    weights B H q (by omega) g root μ a *ᵥ pin B H ℓ =
      fun i => ℓ (rowPolynomial q (by omega) g root a (B i.1) i.2.val μ) := by
  funext i
  apply coordinates_pair
  exact fun _ he => row_supported hq g root a (B i.1) i.2.val μ i.2.property hμt hμ he

/-- One nonzero test supported in the box suffices for nonvanishing of the concrete pin. -/
theorem exists_nonzero_pin (B : Basis β k E) (H : ℕ) (ℓ : Laurent σ E →ₗ[k] k)
    (f : Laurent σ E) (hs : ∀ e ∈ f.coeff.support, InBox H e) (hne : ℓ f ≠ 0) :
    ∃ i, pin B H ℓ i ≠ 0 := by
  by_contra! h
  apply hne
  rw [← coordinates_pair B H ℓ f hs]
  simp [h]

end ResiduePins

end BorderVNP
end Computability
end OAI
