import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeCRT
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimePresentation
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Cyclic columns of the prime-axis transform

The scalar coordinate and the quadratic-binomial monomials label the output
rows. Products of columns have the same structure constants as the original
endpoint of the deformation.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial TensorProduct Module Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] [Nontrivial R] {m p : ℕ} {ρ β : R}

/-- Output coordinates of an axis, with the scalar at `none`. -/
abbrev PrimeAxisRow (m : ℕ) := Option (Fin 2 × Fin m)

/-- Power basis of the active factor of a prime axis. -/
noncomputable abbrev primeAxisActiveBasis (hm : 0 < m) (ρ β : R) :=
  (quadraticBasis ρ).tensorProduct (binomialBasis hm β)

/-- The scalar and active monomials together give the full output basis. -/
noncomputable def primeAxisOutputBasis (hm : 0 < m) (ρ β : R) :
    Basis (PrimeAxisRow m) R (R × (QuadraticAxis ρ ⊗[R] BinomialAxis m β)) :=
  ((Basis.singleton PUnit.{1} R).prod (primeAxisActiveBasis hm ρ β)).reindex
    ((Equiv.sumComm _ _).trans (Equiv.optionEquivSumPUnit _).symm)

@[simp] theorem primeAxisOutputBasis_repr_none (hm : 0 < m) (x) :
    (primeAxisOutputBasis hm ρ β).repr x none = x.1 := by
  simp [primeAxisOutputBasis, Basis.repr_reindex]

@[simp] theorem primeAxisOutputBasis_repr_some (hm : 0 < m) (x) (k) :
    (primeAxisOutputBasis hm ρ β).repr x (some k) = (primeAxisActiveBasis hm ρ β).repr x.2 k := by
  simp [primeAxisOutputBasis, Basis.repr_reindex]

/-- Coefficient of an active monomial product at the undeformed endpoint. -/
noncomputable def primeAxisActiveCoeff (ρ β : R) (a b k : Fin 2 × Fin m) : R :=
  (quadraticCoeff ρ a.1 b.1 k.1 * binomialCoeff β a.2 b.2 k.2).eval 1

theorem primeAxisActiveBasis_repr_mul (hm : 0 < m) (a b k : Fin 2 × Fin m) :
    let B := primeAxisActiveBasis hm ρ β
    B.repr (B a * B b) k = primeAxisActiveCoeff ρ β a b k := by
  dsimp only
  rcases k with ⟨i,j⟩
  let φ : R[X] →+* R := Polynomial.evalRingHom (1 : R)
  have hc : φ (C ρ * X) = ρ := by simp [φ]
  have hb : φ (binomial β) = β := by simp [φ, binomial]
  have hq := quadraticBasis_repr_mul φ ρ a.1 b.1 i
  have hy := binomialBasis_repr_mul φ β hm a.2 b.2 j
  dsimp only at hq hy
  rw [hc] at hq
  rw [hb] at hy
  simp only [primeAxisActiveBasis, Basis.tensorProduct_apply', Algebra.TensorProduct.tmul_mul_tmul,
    Basis.tensorProduct_repr_tmul_apply, hq, hy, smul_eq_mul, primeAxisActiveCoeff, eval_mul]
  exact mul_comm ..

/-- Compose the scalar splitting with the power-basis presentation of its second factor. -/
noncomputable def primeAxisProductEquiv {A : Type*} [CommRing A] [Algebra R A]
    (crt : BinomialAxis p (1 : R) ≃ₐ[R] R × A)
    (present : (QuadraticAxis ρ ⊗[R] BinomialAxis m β) ≃ₐ[R] A) :
    BinomialAxis p (1 : R) ≃ₐ[R] R × (QuadraticAxis ρ ⊗[R] BinomialAxis m β) :=
  crt.trans ((AlgEquiv.refl : R ≃ₐ[R] R).prodCongr present.symm)

variable [Fact p.Prime]
variable (hm : 0 < m) (e : BinomialAxis p (1 : R) ≃ₐ[R] R × (QuadraticAxis ρ ⊗[R] BinomialAxis m β))

/-- Matrix from cyclic coordinates to scalar and active coordinates. -/
noncomputable def primeAxisMatrix : Matrix (PrimeAxisRow m) (ZMod p) R :=
  LinearMap.toMatrix (primeCyclicBasis R p) (primeAxisOutputBasis hm ρ β) e.toLinearMap

/-- The inverse basis change recovers the cyclic coordinates. -/
noncomputable def primeAxisInvMatrix : Matrix (ZMod p) (PrimeAxisRow m) R :=
  LinearMap.toMatrix (primeAxisOutputBasis hm ρ β) (primeCyclicBasis R p) e.symm.toLinearMap

@[simp] theorem primeAxisInvMatrix_mul :
    primeAxisInvMatrix hm e * primeAxisMatrix hm e = 1 := by
  rw [primeAxisInvMatrix, primeAxisMatrix, ← LinearMap.toMatrix_comp]
  exact (show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by apply LinearMap.ext; exact fun x => e.symm_apply_apply x) ▸
    LinearMap.toMatrix_id _

@[simp] theorem primeAxisMatrix_mul_inv :
    primeAxisMatrix hm e * primeAxisInvMatrix hm e = 1 := by
  rw [primeAxisInvMatrix, primeAxisMatrix, ← LinearMap.toMatrix_comp]
  exact (show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by apply LinearMap.ext; exact fun x => e.apply_symm_apply x) ▸
    LinearMap.toMatrix_id _

theorem primeAxisMatrix_none (a : ZMod p) : primeAxisMatrix hm e none a =
    (e (primeCyclicBasis R p a)).1 := by
  simp [primeAxisMatrix, LinearMap.toMatrix_apply]

theorem primeAxisMatrix_some (a : ZMod p) (k : Fin 2 × Fin m) :
    primeAxisMatrix hm e (some k) a = (primeAxisActiveBasis hm ρ β).repr (e (primeCyclicBasis R p a)).2 k := by
  simp [primeAxisMatrix, LinearMap.toMatrix_apply]

theorem primeAxisMatrix_add_none (a b : ZMod p) :
    primeAxisMatrix hm e none (a+b) = primeAxisMatrix hm e none a * primeAxisMatrix hm e none b := by
  simp [primeAxisMatrix_none, primeCyclicBasis_add]

theorem primeAxisMatrix_add_some (a b : ZMod p) (k : Fin 2 × Fin m) :
    primeAxisMatrix hm e (some k) (a+b) = multiply (primeAxisActiveCoeff ρ β)
      (fun j => primeAxisMatrix hm e (some j) a) (fun j => primeAxisMatrix hm e (some j) b) k := by
  let B := primeAxisActiveBasis hm ρ β
  let x := (e (primeCyclicBasis R p a)).2
  let y := (e (primeCyclicBasis R p b)).2
  simp only [primeAxisMatrix_some, primeCyclicBasis_add, map_mul, Prod.snd_mul]
  change B.coord k (x*y) = _
  calc
    _ = B.coord k ((∑ i, B.repr x i • B i) * (∑ j, B.repr y j • B j)) := by
      rw [B.sum_repr, B.sum_repr]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
        smul_eq_mul, Basis.coord_apply, B, primeAxisActiveBasis_repr_mul, multiply, x, y]
      exact Finset.sum_comm

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
