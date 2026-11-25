import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionDeformationSplit
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionQuadraticIso
import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionBinomialIso
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # The tensor product of the integral summand's axis algebras

The monomials in the quadratic and binomial generators give a basis for the summand. In
this basis, every multiplication is given by the products of the axis structure constants.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial TensorProduct Module
open scoped BigOperators

variable {R A σ : Type*} [CommRing R] [CommRing A]

/-- An active block after specialization, with one quadratic and one binomial algebra per axis. -/
abbrev Block (m : σ → ℕ) (c b : σ → A) :=
  ⨂[A] i, QuadraticAxis (c i) ⊗[A] BinomialAxis (m i) (b i)

/-- Power coordinates for the quadratic monic quotient. -/
noncomputable def quadraticBasis (c : A) : Basis (Fin 2) A (QuadraticAxis c) :=
  (QuadraticAlgebra.basis (-c) (-1)).map (quadraticAxisEquiv c).symm.toLinearEquiv

theorem quadraticBasis_apply (c : A) (j : Fin 2) :
    quadraticBasis c j = AdjoinRoot.root (quadraticAxisPoly c) ^ j.val := by
  apply (quadraticAxisEquiv c).injective
  simp only [quadraticBasis, Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, map_pow, quadraticAxisEquiv_root]
  fin_cases j
  · exact (QuadraticAlgebra.basis_apply_zero ..).trans (pow_zero _).symm
  · exact (QuadraticAlgebra.basis_apply_one ..).trans (pow_one _).symm

/-- Power coordinates for the binomial monic quotient. -/
noncomputable def binomialBasis [Nontrivial A] {m : ℕ} (hm : 0 < m) (b : A) :
    Basis (Fin m) A (BinomialAxis m b) :=
  (AdjoinRoot.powerBasis' (monic_X_pow_sub_C b hm.ne')).basis.reindex
    (finCongr (show ((X : A[X])^m - C b).natDegree = m from natDegree_X_pow_sub_C))

theorem binomialBasis_apply [Nontrivial A] {m : ℕ} (hm : 0 < m) (b : A) (j : Fin m) :
    binomialBasis hm b j = AdjoinRoot.root ((X : A[X])^m - C b) ^ j.val := by
  simp [binomialBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

private theorem repr_of_sum_smul {B κ : Type*} [Fintype κ] [CommRing B] [Algebra A B]
    (basis : Basis κ A B) (x : B) (v : κ → A) (h : ∑ j, v j • basis j = x) (k : κ) :
    basis.repr x k = v k := by
  have hv : basis.equivFun.symm v = x := by rwa [Basis.equivFun_symm_apply]
  exact congrFun ((basis.equivFun.symm_apply_eq).mp hv).symm k

theorem quadraticBasis_repr_mul (φ : R[X] →+* A) (ρ : R) (a b k : Fin 2) :
    let B := quadraticBasis (φ (C ρ * X))
    B.repr (B a * B b) k = φ (quadraticCoeff ρ a b k) := by
  dsimp only
  let c := φ (C ρ * X)
  let g := algebraMap A (QuadraticAxis c)
  let u := AdjoinRoot.root (quadraticAxisPoly c)
  have h := quadraticAxis_root_relation c
  have hu : u^2 = -u - (g.comp φ) (C ρ * X) := by
    change u^2 + u + g c = 0 at h
    change u^2 = -u - g c
    linear_combination h
  apply repr_of_sum_smul
  simpa only [Algebra.smul_def, quadraticBasis_apply, RingHom.comp_apply] using
    quadratic_normal_form (g.comp φ) ρ u hu a b

theorem binomialBasis_repr_mul [Nontrivial A] (φ : R[X] →+* A) (β : R)
    {m : ℕ} (hm : 0 < m) (a b k : Fin m) :
    let B := binomialBasis hm (φ (binomial β))
    B.repr (B a * B b) k = φ (binomialCoeff β a b k) := by
  dsimp only
  let e := φ (binomial β)
  let g := algebraMap A (BinomialAxis m e)
  let y := AdjoinRoot.root ((X : A[X])^m - C e)
  apply repr_of_sum_smul
  simpa only [Algebra.smul_def, binomialBasis_apply, RingHom.comp_apply] using
    binomial_normal_form (g.comp φ) β y (binomialAxis_root_pow m e) a b

variable [Fintype σ] [DecidableEq σ]

/-- The tensor of the quadratic and binomial power bases on all active axes. -/
noncomputable def blockBasis [Nontrivial A] (m : σ → ℕ) (hm : ∀ i, 0 < m i) (c b : σ → A) :
    Basis (Address m) A (Block m c b) :=
  Basis.piTensorProduct (fun i => (quadraticBasis (c i)).tensorProduct (binomialBasis (hm i) (b i)))

omit [DecidableEq σ] in
/-- The structure constants in the tensor product's actual power basis agree with
the polynomials reduced on each axis. -/
theorem blockBasis_repr_mul [Nontrivial A] (φ : R[X] →+* A) (ρ β : σ → R)
    (m : σ → ℕ) (hm : ∀ i, 0 < m i) (a b k : Address m) :
    let B := blockBasis m hm (fun i => φ (C (ρ i)*X)) (fun i => φ (binomial (β i)))
    B.repr (B a * B b) k = φ (integralCoeff ρ β m a b k) := by
  dsimp only
  simp only [blockBasis, Basis.piTensorProduct_apply, PiTensorProduct.tprod_mul_tprod,
    Basis.piTensorProduct_repr_tprod_apply, Pi.mul_apply, Basis.tensorProduct_apply',
    Algebra.TensorProduct.tmul_mul_tmul, integralCoeff, map_prod, map_mul]
  apply Finset.prod_congr rfl
  intro i _
  rw [Basis.tensorProduct_repr_tmul_apply _ _ _ _ (k i).1 (k i).2,
    quadraticBasis_repr_mul, binomialBasis_repr_mul, smul_eq_mul, mul_comm]

/-- Full block multiplication in coordinates at an arbitrary specialization. -/
theorem blockBasis_mul [Nontrivial A] (φ : R[X] →+* A) (ρ β : σ → R)
    (m : σ → ℕ) (hm : ∀ i, 0 < m i) :
    let B := blockBasis m hm (fun i => φ (C (ρ i)*X)) (fun i => φ (binomial (β i)))
    ∀ x y, B.equivFun (x*y) = multiply (fun a b k => φ (integralCoeff ρ β m a b k))
      (B.equivFun x) (B.equivFun y) := by
  intro B x y
  let T := Block m (fun i => φ (C (ρ i)*X)) (fun i => φ (binomial (β i)))
  let : IsScalarTower A T T := IsScalarTower.right (R := A) (A := T)
  let : SMulCommClass A T T := Algebra.to_smulCommClass (R := A) (A := T)
  funext k
  calc
    _ = B.equivFun ((∑ a, (B.repr x a) • B a) * (∑ b, (B.repr y b) • B b)) k := by
      rw [B.sum_repr, B.sum_repr]
    _ = _ := by
      change B.coord k _ = _
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum, map_sum, multiply]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [smul_mul_smul_comm, map_smul, smul_eq_mul, Basis.coord_apply]
      rw [show B.repr (B a * B b) k = _ from blockBasis_repr_mul φ ρ β m hm a b k]
      rfl

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
