import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Presentation of the nonscalar factor on a prime axis

The quadratic and binomial relations induce an algebra map from the tensor
of the two monic quotients. When the vectors `Y^j, U*Y^j` form a basis,
this map identifies the two algebras in their indicated power coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial TensorProduct Module

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {m : ℕ} {ρ β : R} {U Y : A}

/-- Evaluate the two defining generators in a commutative algebra. -/
noncomputable def primeAxisPresentationHom
    (hU : U^2 + U + algebraMap R A ρ = 0) (hY : Y^m = algebraMap R A β) :
    (QuadraticAxis ρ ⊗[R] BinomialAxis m β) →ₐ[R] A :=
  Algebra.TensorProduct.lift
    (AdjoinRoot.liftAlgHom (quadraticAxisPoly ρ) (Algebra.ofId R A) U
      (by simpa [quadraticAxisPoly] using hU))
    (AdjoinRoot.liftAlgHom ((X : R[X])^m - C β) (Algebra.ofId R A) Y
      (by simpa using sub_eq_zero.mpr hY))
    (fun _ _ => Commute.all ..)

/-- Evaluation carries the tensor of power basis vectors to its monomial. -/
@[simp] theorem primeAxisPresentationHom_basis [Nontrivial R] (hm : 0 < m)
    (hU : U^2 + U + algebraMap R A ρ = 0) (hY : Y^m = algebraMap R A β)
    (ij : Fin 2 × Fin m) :
    primeAxisPresentationHom hU hY
      (((quadraticBasis ρ).tensorProduct (binomialBasis hm β)) ij) =
      U^ij.1.val * Y^ij.2.val := by
  simp only [primeAxisPresentationHom, Basis.tensorProduct_apply', Algebra.TensorProduct.lift_tmul,
    quadraticBasis_apply, binomialBasis_apply, map_pow, AdjoinRoot.liftAlgHom_root]

/-- The indicated target basis gives the presentation as the tensor of the two axis algebras. -/
noncomputable def primeAxisPresentationEquiv [Nontrivial R] (hm : 0 < m)
    (hU : U^2 + U + algebraMap R A ρ = 0) (hY : Y^m = algebraMap R A β)
    (e : Basis (Fin 2 × Fin m) R A)
    (e₀ : ∀ j, e (0,j) = Y^j.val) (e₁ : ∀ j, e (1,j) = U * Y^j.val) :
    (QuadraticAxis ρ ⊗[R] BinomialAxis m β) ≃ₐ[R] A := by
  let b := (quadraticBasis ρ).tensorProduct (binomialBasis hm β)
  let f := primeAxisPresentationHom hU hY
  let l := b.equiv e (Equiv.refl _)
  have hf : f.toLinearMap = l.toLinearMap := by
    apply b.ext
    rintro ⟨i,j⟩
    change primeAxisPresentationHom hU hY (b (i,j)) = l (b (i,j))
    rw [Basis.equiv_apply, primeAxisPresentationHom_basis]
    fin_cases i <;> simp [e₀, e₁]
  exact AlgEquiv.ofBijective f (show Function.Bijective f.toLinearMap by rw [hf]; exact l.bijective)

/-- In the presentation equivalence the source basis is sent to the chosen target basis. -/
@[simp] theorem primeAxisPresentationEquiv_basis [Nontrivial R] (hm : 0 < m)
    (hU : U^2 + U + algebraMap R A ρ = 0) (hY : Y^m = algebraMap R A β)
    (e : Basis (Fin 2 × Fin m) R A)
    (e₀ : ∀ j, e (0,j) = Y^j.val) (e₁ : ∀ j, e (1,j) = U * Y^j.val)
    (ij : Fin 2 × Fin m) :
    primeAxisPresentationEquiv hm hU hY e e₀ e₁
      (((quadraticBasis ρ).tensorProduct (binomialBasis hm β)) ij) = e ij := by
  change primeAxisPresentationHom hU hY _ = _
  rw [primeAxisPresentationHom_basis]
  rcases ij with ⟨i,j⟩
  fin_cases i <;> simp [e₀, e₁]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
