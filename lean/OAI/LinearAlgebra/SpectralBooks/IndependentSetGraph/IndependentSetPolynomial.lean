import OAI.LinearAlgebra.SpectralBooks.IndependentSetGrid.IndependentSetGrid
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fintype.EquivFin

/-! # Independent-set polynomials and their projections

The two endpoint maps give one orientation of every edge. The occupation
condition depends only on the unordered pair of endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace IndependentSetGraph

open scoped Classical BigOperators
variable {V E σ τ R : Type*} [CommSemiring R]

def independent (left right : E → V) (b : V → Bool) : Prop :=
  ∀ e, b (left e) = true → b (right e) ≠ true

def weightedSum [Fintype V] (left right : E → V) (w : V → Bool → R) : R :=
  ∑ b : V → Bool, if independent left right b then ∏ v, w v (b v) else 0

def polynomial (R : Type*) [CommSemiring R] [Fintype V] (left right : E → V) :
    MvPolynomial (V × Bool) R :=
  weightedSum left right (fun v b => MvPolynomial.X (v,b))

abbrev ProjectionAtom (R σ : Type*) := σ ⊕ R

def atomPolynomial (a : ProjectionAtom R σ) : MvPolynomial σ R :=
  a.elim MvPolynomial.X MvPolynomial.C

def project (p : σ → ProjectionAtom R τ) (f : MvPolynomial σ R) : MvPolynomial τ R :=
  MvPolynomial.aeval (fun i => atomPolynomial (p i)) f

@[simp] theorem project_X (p : σ → ProjectionAtom R τ) (i : σ) :
    project p (MvPolynomial.X i) = atomPolynomial (p i) := by simp [project]

@[simp] theorem project_C (p : σ → ProjectionAtom R τ) (c : R) :
    project p (MvPolynomial.C c) = MvPolynomial.C c := by simp [project]

theorem map_weightedSum {S : Type*} [CommSemiring S] [Fintype V] (φ : R →+* S)
    (left right : E → V) (w : V → Bool → R) :
    φ (weightedSum left right w) = weightedSum left right (fun v b => φ (w v b)) := by
  simp [weightedSum, map_sum, apply_ite, map_prod]

theorem project_polynomial [Fintype V] (p : V × Bool → ProjectionAtom R τ) (left right : E → V) :
    project p (polynomial R left right) =
      weightedSum left right (fun v b => atomPolynomial (p (v,b))) := by
  unfold project polynomial
  simp only [map_sum, weightedSum, apply_ite, map_prod, MvPolynomial.aeval_X, map_zero]

theorem polynomial_isHomogeneous [Fintype V] (left right : E → V) :
    (polynomial R left right).IsHomogeneous (Fintype.card V) := by
  unfold polynomial weightedSum
  apply MvPolynomial.IsHomogeneous.sum
  intro b _
  split
  · simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ : V => 1)
      (fun i _ => MvPolynomial.isHomogeneous_X (R := R) (i, b i))
  · exact MvPolynomial.isHomogeneous_zero _ _ _

end IndependentSetGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
