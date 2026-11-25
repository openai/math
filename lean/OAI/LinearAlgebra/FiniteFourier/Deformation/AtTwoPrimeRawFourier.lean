import OAI.LinearAlgebra.FiniteFourier.AtTwoPrimeFourierBasis
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeCRT
import OAI.LinearAlgebra.FiniteFourier.Cyclic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Signed-orbit Fourier coordinates on the full prime cyclic algebra

The monomial at the zero residue stays in place. On each of the two signed
orbits, synthesis uses the negative-sign Fourier matrix and analysis uses
the positive-sign Fourier matrix divided by the orbit length.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix Module Polynomial
open scoped BigOperators Kronecker

variable (R : Type*) [CommRing R] {p : ℕ} [Fact p.Prime] (C : PrimeAxisCosets p)

/-- One constant monomial and two equal-length signed rows. -/
abbrev AtTwoRawIndex (m : ℕ) := PUnit.{1} ⊕ (Bool × Fin m)

/-- Enumerate all residues, putting zero first and the signed power orbits next. -/
noncomputable def atTwoRawIndex : AtTwoRawIndex ((p-1)/2) ≃ ZMod p := by
  let e : PUnit ≃ {a : ZMod p // a = 0} :=
    ⟨fun _ => ⟨0,rfl⟩, fun _ => PUnit.unit, fun _ => rfl, fun a => Subtype.ext a.2.symm⟩
  exact (e.sumCongr (C.equiv.trans unitsEquivNeZero)).trans (Equiv.sumCompl (· = (0 : ZMod p)))

@[simp] theorem atTwoRawIndex_inl (v : PUnit) : atTwoRawIndex C (.inl v) = 0 := rfl

@[simp] theorem atTwoRawIndex_inr (ct : Bool × Fin ((p-1)/2)) :
    atTwoRawIndex C (.inr ct) = (C.equiv ct : ZMod p) := rfl

variable {R} {m : ℕ}

/-- A single Fourier matrix acting on each signed row, fixing the zero address. -/
def atTwoRawTransform (D : Matrix (Fin m) (Fin m) R) : Matrix (AtTwoRawIndex m) (AtTwoRawIndex m) R :=
  fromBlocks 1 0 0 ((1 : Matrix Bool Bool R) ⊗ₖ D)

theorem atTwoRawTransform_mul (D E : Matrix (Fin m) (Fin m) R) :
    atTwoRawTransform D * atTwoRawTransform E = atTwoRawTransform (D*E) := by
  simp [atTwoRawTransform, fromBlocks_multiply, ← mul_kronecker_mul]

@[simp] theorem atTwoRawTransform_one : atTwoRawTransform (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  simp [atTwoRawTransform]

private theorem atTwoDft_leftInverse (u : Rˣ) (hm : IsUnit (m:R)) (hu : u^m = 1)
    (hs : ∀ i j : Fin m, i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val)) :
    ((↑hm.unit⁻¹ : R) • dftMatrix m (u : R)) * dftMatrix m (↑u⁻¹ : R) = 1 := by
  rw [Matrix.smul_mul]
  ext i j
  have hentry : (dftMatrix m (u:R) * dftMatrix m (↑u⁻¹ : R)) i j =
      if j = i then (m:R) else 0 := by
    rw [Matrix.mul_apply, ← cyclicCharacter_orthogonal u hu hs j i]
    apply Finset.sum_congr rfl
    intro t _
    simp [dftMatrix, ← inv_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
  rw [Matrix.smul_apply, hentry, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, smul_eq_mul] using hm.val_inv_mul
  · simp [hij, Ne.symm hij]

local notation "mₚ" => ((p-1)/2 : ℕ)
variable (R) [Nontrivial R]

/-- The standard cyclic power basis in signed row order. -/
noncomputable def atTwoRawMonomialBasis : Basis (AtTwoRawIndex mₚ) R (BinomialAxis p (1:R)) :=
  (primeCyclicBasis R p).reindex (atTwoRawIndex C).symm

@[simp] theorem atTwoRawMonomialBasis_apply (i : AtTwoRawIndex mₚ) :
    atTwoRawMonomialBasis R C i = primeCyclicBasis R p (atTwoRawIndex C i) := by
  simp [atTwoRawMonomialBasis]

variable (u : Rˣ) (hm : IsUnit (((p-1)/2 : ℕ) : R)) (hu : u^((p-1)/2) = 1)
variable (hs : ∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))

include hu hs in
omit [Nontrivial R] [Fact p.Prime] in
private theorem rawInverse :
    atTwoRawTransform ((↑hm.unit⁻¹ : R) • dftMatrix mₚ (u:R)) *
      atTwoRawTransform (dftMatrix mₚ (↑u⁻¹ : R)) = 1 := by
  rw [atTwoRawTransform_mul, atTwoDft_leftInverse u hm hu hs, atTwoRawTransform_one]

/-- Fourier-transform the two signed cycles inside the full cyclic algebra. -/
noncomputable def atTwoRawFourierBasis : Basis (AtTwoRawIndex mₚ) R (BinomialAxis p (1:R)) :=
  let b := atTwoRawMonomialBasis R C
  b.map (Matrix.toLinearEquiv b _ (Matrix.isUnit_det_of_left_inverse (rawInverse R u hm hu hs)))

/-- Synthesis from Fourier coordinates, before the permutation to residue order. -/
theorem atTwoRawFourier_synthesis :
    (atTwoRawMonomialBasis R C).toMatrix (atTwoRawFourierBasis R C u hm hu hs) =
      atTwoRawTransform (dftMatrix mₚ (↑u⁻¹ : R)) := by
  let b := atTwoRawMonomialBasis R C
  let D := atTwoRawTransform (dftMatrix mₚ (↑u⁻¹ : R))
  ext i j
  rw [Basis.toMatrix_apply, atTwoRawFourierBasis, Basis.map_apply, Matrix.toLinearEquiv_apply]
  simpa only [LinearMap.toMatrix_apply] using congrArg (fun M => M i j) (LinearMap.toMatrix_toLin b b D)

/-- Analysis into Fourier coordinates, after the permutation from residue order. -/
theorem atTwoRawFourier_analysis :
    (atTwoRawFourierBasis R C u hm hu hs).toMatrix (atTwoRawMonomialBasis R C) =
      atTwoRawTransform ((↑hm.unit⁻¹ : R) • dftMatrix mₚ (u:R)) := by
  apply Matrix.left_inv_eq_left_inv _ (rawInverse R u hm hu hs)
  rw [← atTwoRawFourier_synthesis R C u hm hu hs, Basis.toMatrix_mul_toMatrix_flip]

private theorem rawFourier_expansion (i : AtTwoRawIndex mₚ) :
    atTwoRawFourierBasis R C u hm hu hs i =
      ∑ k, atTwoRawTransform (dftMatrix mₚ (↑u⁻¹ : R)) k i • atTwoRawMonomialBasis R C k :=
  by rw [atTwoRawFourierBasis, Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]

@[simp] theorem atTwoRawFourierBasis_inl (v : PUnit) :
    atTwoRawFourierBasis R C u hm hu hs (.inl v) = 1 := by
  rw [rawFourier_expansion, Fintype.sum_sum_type]
  simp [atTwoRawTransform, primeCyclicBasis_apply]

theorem atTwoRawFourierBasis_inr (c : Bool) (j : Fin mₚ) :
    atTwoRawFourierBasis R C u hm hu hs (.inr (c,j)) =
      ∑ t : Fin mₚ, (↑((u^j.val)⁻¹) : R)^t.val • primeCyclicBasis R p (C.equiv (c,t)) := by
  rw [rawFourier_expansion, Fintype.sum_sum_type]
  cases c <;> simp [atTwoRawTransform, Fintype.sum_prod_type,
    Matrix.one_apply, dftMatrix, ← inv_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm]

/-- The original constant monomial evaluates to one on both CRT factors. -/
theorem primeCyclicCRT_rawFourier_inl (hp : IsUnit (p:R)) (v : PUnit) :
    primeCyclicCRT R p hp (atTwoRawFourierBasis R C u hm hu hs (.inl v)) = (1,1) := by
  rw [atTwoRawFourierBasis_inl, map_one]
  rfl

/-- Only the zero frequencies have scalar CRT component. The second component
is exactly the corresponding orbit Fourier vector of the cyclotomic quotient. -/
theorem primeCyclicCRT_rawFourier_inr (hp : IsUnit (p:R)) (hmpos : 0 < mₚ)
    (c : Bool) (j : Fin mₚ) :
    primeCyclicCRT R p hp (atTwoRawFourierBasis R C u hm hu hs (.inr (c,j))) =
      (if j.val = 0 then (mₚ:R) else 0, atTwoPrimeFourier R C u c j) := by
  rw [atTwoRawFourierBasis_inr, map_sum]
  simp only [map_smul, primeCyclicCRT_basis]
  apply Prod.ext
  · simpa [Prod.fst_sum, Fin.ext_iff] using
      cyclicCharacter_orthogonal u hu hs j ⟨0,hmpos⟩
  · simp [Prod.snd_sum, atTwoPrimeFourier, orbitFourier, atTwoPrimeMonomialBasis_apply]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
