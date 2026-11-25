import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicPrimeCoordinates
import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationBlock
import Mathlib.LinearAlgebra.Basis.Prod

/-! # Scalar extension of a dyadic-list prime-axis matrix

All choices in the binomial presentation are made over the coefficient order.
The same coefficient matrices then act on the two jet rings.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace Deformation

open Polynomial Module Matrix
open scoped BigOperators

/-- Chosen unit diagonal and binomial presentation for a prime axis. -/
structure DyadicPrimeAxis (R : Type*) [CommRing R] [Nontrivial R] (p : ℕ) [Fact p.Prime]
    (C : PrimeAxisOrbit p) (u : Rˣ) (hm : IsUnit ((p-1 : ℕ) : R)) where
  beta : Rˣ
  diagonal : Fin (p-1) → Rˣ
  equiv : BinomialAxis p (1 : R) ≃ₐ[R] R × BinomialAxis (p-1) (beta:R)
  diagonal_zero : (diagonal ⟨0, by have := (Fact.out : p.Prime).two_le; omega⟩ : R) = -1
  transform (a : R) (v : Fin (p-1) → R) :
    equiv (algebraMap R _ a + ∑ t, v t • primeCyclicBasis R p (C.equiv t)) =
      (a + ∑ t, v t, algebraMap R _ a + ∑ j,
        (((↑hm.unit⁻¹ : R) * dyadicPrimeSums u v j) * (diagonal j : R)) •
        binomialBasis (by have := (Fact.out : p.Prime).two_le; omega) (beta:R) j)

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]

/-- Choose the axis presentation from a separated system of roots. -/
def dyadicPrimeAxis (C : PrimeAxisOrbit p) (u : Rˣ) (hodd : 1 < p-1) (hpR : IsUnit (p:R))
    (hm : IsUnit ((p-1 : ℕ) : R)) (hu : u^(p-1) = 1)
    (hs : ∀ i j : Fin (p-1), i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    DyadicPrimeAxis R p C u hm := by
  apply Classical.choice
  obtain ⟨β,d,e,hz,ht⟩ := exists_dyadicPrimeCoordinates C u hodd hpR hm hu hs
  exact ⟨⟨β,d,e,hz,ht⟩⟩

namespace DyadicPrimeAxis

variable {C : PrimeAxisOrbit p} {u : Rˣ} {hm : IsUnit ((p-1 : ℕ) : R)}
    (a : DyadicPrimeAxis R p C u hm)
local notation "m" => (p-1)

private theorem mpos : 0 < m := by have := (Fact.out : p.Prime).two_le; omega

/-- Power coordinates for the two target factors, with the scalar channel first. -/
def outputBasis : Basis (Option (Fin m)) R (R × BinomialAxis m (a.beta:R)) :=
  ((Basis.singleton PUnit.{1} R).prod (binomialBasis mpos (a.beta:R))).reindex
    ((Equiv.sumComm _ _).trans (Equiv.optionEquivSumPUnit _).symm)

@[simp] theorem outputBasis_none (x) : a.outputBasis.repr x none = x.1 := by
  simp [outputBasis, Basis.repr_reindex]

@[simp] theorem outputBasis_some (x) (k) :
    a.outputBasis.repr x (some k) = (binomialBasis mpos (a.beta:R)).repr x.2 k := by
  simp [outputBasis, Basis.repr_reindex]

/-- Matrix of the chosen algebra map in cyclic and split power coordinates. -/
def forward : Matrix (Option (Fin m)) (ZMod p) R :=
  LinearMap.toMatrix (primeCyclicBasis R p) a.outputBasis a.equiv.toLinearMap

/-- Inverse matrix over the same base order. -/
def backward : Matrix (ZMod p) (Option (Fin m)) R :=
  LinearMap.toMatrix a.outputBasis (primeCyclicBasis R p) a.equiv.symm.toLinearMap

@[simp] theorem backward_mul_forward : a.backward * a.forward = 1 := by
  rw [backward, forward, ← LinearMap.toMatrix_comp]
  exact (show a.equiv.symm.toLinearMap.comp a.equiv.toLinearMap = LinearMap.id by
    apply LinearMap.ext; exact fun x => a.equiv.symm_apply_apply x) ▸ LinearMap.toMatrix_id _

@[simp] theorem forward_mul_backward : a.forward * a.backward = 1 := by
  rw [backward, forward, ← LinearMap.toMatrix_comp]
  exact (show a.equiv.toLinearMap.comp a.equiv.symm.toLinearMap = LinearMap.id by
    apply LinearMap.ext; exact fun x => a.equiv.apply_symm_apply x) ▸ LinearMap.toMatrix_id _

theorem forward_none (g : ZMod p) : a.forward none g = (a.equiv (primeCyclicBasis R p g)).1 := by
  simp [forward, LinearMap.toMatrix_apply]

theorem forward_some (g : ZMod p) (k : Fin m) :
    a.forward (some k) g = (binomialBasis mpos (a.beta:R)).repr (a.equiv (primeCyclicBasis R p g)).2 k := by
  simp [forward, LinearMap.toMatrix_apply]

@[simp] theorem forward_none_zero : a.forward none 0 = 1 := by
  rw [forward_none, primeCyclicBasis_apply]
  simp

@[simp] theorem forward_some_zero (k : Fin m) :
    a.forward (some k) 0 = if k = ⟨0,mpos⟩ then 1 else 0 := by
  rw [forward_some, primeCyclicBasis_apply]
  simp only [ZMod.val_zero, pow_zero, map_one, Prod.snd_one]
  have h : binomialBasis mpos (a.beta:R) ⟨0,mpos (p := p)⟩ = 1 := by simp [binomialBasis_apply]
  rw [← h, Basis.repr_self, Finsupp.single_apply]
  simp [eq_comm]

private theorem equiv_orbit (t : Fin m) :
    a.equiv (primeCyclicBasis R p (C.equiv t)) =
      (1, ∑ j : Fin m, (((↑hm.unit⁻¹ : R) * (u:R)^(j.val * t.val)) *
        (a.diagonal j : R)) • binomialBasis mpos (a.beta:R) j) := by
  classical
  simpa [dyadicPrimeSums, mul_ite, ite_smul] using
    a.transform 0 (fun i => if i = t then 1 else 0)

@[simp] theorem forward_none_orbit (t : Fin m) : a.forward none (C.equiv t) = 1 := by
  rw [forward_none, equiv_orbit]

theorem forward_some_orbit (k t : Fin m) :
    a.forward (some k) (C.equiv t) =
      (↑hm.unit⁻¹ : R) * (a.diagonal k : R) * (u:R)^(k.val*t.val) := by
  rw [forward_some, equiv_orbit]
  simp only [map_sum, map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  ring

theorem forward_add_none (g t : ZMod p) : a.forward none (g+t) = a.forward none g * a.forward none t := by
  simp [forward_none, primeCyclicBasis_add]

/-- Images of cyclic monomials multiply by the wrapped binomial product. -/
theorem forward_add_some (g t : ZMod p) (k : Fin m) :
    a.forward (some k) (g+t) = multiply (Dyadic.axisCoeff (a.beta:R))
      (fun j => a.forward (some j) g) (fun j => a.forward (some j) t) k := by
  let B := binomialBasis (mpos (p := p)) (a.beta:R)
  let x := (a.equiv (primeCyclicBasis R p g)).2
  let y := (a.equiv (primeCyclicBasis R p t)).2
  simp only [forward_some, primeCyclicBasis_add, map_mul, Prod.snd_mul]
  change B.coord k (x*y) = _
  calc
    _ = B.coord k ((∑ i, B.repr x i • B i) * (∑ j, B.repr y j • B j)) := by
      rw [B.sum_repr, B.sum_repr]
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
        smul_eq_mul, Basis.coord_apply, B, Dyadic.axisBasis_repr_mul, multiply, x, y]
      exact Finset.sum_comm

section Map

variable {S : Type*} [CommRing S] (φ : R →+* S)

@[simp] theorem map_backward_mul_forward : a.backward.map φ * a.forward.map φ = 1 := by
  rw [← Matrix.map_mul, backward_mul_forward, Matrix.map_one] <;> simp

@[simp] theorem map_forward_mul_backward : a.forward.map φ * a.backward.map φ = 1 := by
  rw [← Matrix.map_mul, forward_mul_backward, Matrix.map_one] <;> simp

theorem map_forward_add_none (g t : ZMod p) :
    a.forward.map φ none (g+t) = a.forward.map φ none g * a.forward.map φ none t := by
  simp only [Matrix.map_apply, forward_add_none, map_mul]

theorem map_forward_add_some (g t : ZMod p) (k : Fin m) :
    a.forward.map φ (some k) (g+t) = multiply (Dyadic.axisCoeff (φ (a.beta:R)))
      (fun j => a.forward.map φ (some j) g) (fun j => a.forward.map φ (some j) t) k := by
  simpa only [Matrix.map_apply, map_multiply, Function.comp_def, Dyadic.map_axisCoeff] using
    congrArg φ (a.forward_add_some g t k)

end Map
end DyadicPrimeAxis
end Deformation

end

end FiniteFourier
end LinearAlgebra
end OAI
