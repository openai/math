import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationBlock
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Multiplication under a change of specialized block coordinates -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Matrix

variable {R A σ : Type*} [CommRing R] [CommRing A] [Nontrivial A]
  [Fintype σ] [DecidableEq σ]

/-- To multiply in the target block, pull both inputs back through the coordinate
matrix of the inverse isomorphism, multiply in the source, and transport the output. -/
theorem transport_block_multiply (φ ψ : R[X] →+* A) (ρ β : σ → R)
    (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    (e : Block m (fun i => φ (C (ρ i) * X)) (fun i => φ (binomial (β i))) ≃ₐ[A]
      Block m (fun i => ψ (C (ρ i) * X)) (fun i => ψ (binomial (β i))))
    (x y : Address m → A) :
    let B := blockBasis m hm (fun i => φ (C (ρ i) * X)) (fun i => φ (binomial (β i)))
    let D := blockBasis m hm (fun i => ψ (C (ρ i) * X)) (fun i => ψ (binomial (β i)))
    let F := LinearMap.toMatrix B D e.toAlgHom.toLinearMap
    let G := LinearMap.toMatrix D B e.symm.toAlgHom.toLinearMap
    F *ᵥ multiply (fun a b k => φ (integralCoeff ρ β m a b k)) (G *ᵥ x) (G *ᵥ y) =
      multiply (fun a b k => ψ (integralCoeff ρ β m a b k)) x y := by
  intro B D F G
  obtain ⟨x, rfl⟩ := D.equivFun.surjective x
  obtain ⟨y, rfl⟩ := D.equivFun.surjective y
  have hg (u) : G *ᵥ D.equivFun u = B.equivFun (e.symm u) :=
    LinearMap.toMatrix_mulVec_repr D B e.symm.toAlgHom.toLinearMap u
  have hf (u) : F *ᵥ B.equivFun u = D.equivFun (e u) :=
    LinearMap.toMatrix_mulVec_repr B D e.toAlgHom.toLinearMap u
  rw [hg, hg, ← blockBasis_mul φ ρ β m hm (e.symm x) (e.symm y),
    hf, ← map_mul, e.apply_symm_apply, blockBasis_mul ψ ρ β m hm]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
