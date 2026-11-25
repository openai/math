import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeFactor
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeFrequency
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeMatrix
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeRawFourier

/-! # Residual frequency blocks in the prime-axis conversion

After the two orbit transforms the input Fourier vectors and output
monomials are eigenvectors for the same operator on the CRT product.
Their transition matrix and its inverse act separately on each frequency.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial Module TensorProduct Matrix

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
  {C : PrimeAxisCosets p} {u : Rˣ} {hp7 : 7 ≤ p}

local notation "mₚ" => (p - 1) / 2
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)
local notation "ρₚ" => (((p + 1) / 4 : ℕ) : R)

variable (F : AtTwoPrimeFactor R C u hp7) (hpu : IsUnit (p : R))
  (hm : IsUnit (((p-1)/2 : ℕ) : R)) (hu : u^((p-1)/2) = 1)
  (hs : ∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))

omit [Fact p.Prime] in
private theorem hpos (h7 : 7 ≤ p) : 0 < mₚ := by omega

/-- The raw orbital Fourier vectors in the common CRT product, indexed in output order. -/
noncomputable def primeAxisOrbitRows : Basis (PrimeAxisRow mₚ) R (R × Aₚ) :=
  ((atTwoRawFourierBasis R C u hm hu hs).map (primeCyclicCRT R p hpu).toLinearEquiv).reindex
    (primeAxisSignedIndex mₚ).symm

/-- The scalar and binomial-quadratic monomials viewed in the common CRT product. -/
noncomputable def primeAxisMonomialRows : Basis (PrimeAxisRow mₚ) R (R × Aₚ) :=
  (primeAxisOutputBasis (hpos hp7) ρₚ (F.beta:R)).map
    (((AlgEquiv.refl : R ≃ₐ[R] R)).prodCongr F.equiv).toLinearEquiv

private noncomputable abbrev freqOp (C : PrimeAxisCosets p) : Module.End R (R × Aₚ) :=
  (LinearMap.id : Module.End R R).prodMap (primeAxisAction R p C.generator).toLinearMap

private theorem orbitRows_eigen (a : PrimeAxisRow mₚ) :
    freqOp (R := R) C (primeAxisOrbitRows (C := C) (u := u) hpu hm hu hs a) =
      (u:R)^(primeAxisFrequency (hpos hp7) a).val • primeAxisOrbitRows (C := C) (u := u) hpu hm hu hs a := by
  cases a with
  | none =>
    simp [primeAxisOrbitRows, primeAxisFrequency, freqOp]
  | some a =>
    rcases a with ⟨i,j⟩
    simp only [primeAxisOrbitRows, Basis.reindex_apply, Equiv.symm_symm, primeAxisSignedIndex_some,
      Basis.map_apply, AlgEquiv.toLinearEquiv_apply, primeCyclicCRT_rawFourier_inr R C u hm hu hs hpu (hpos hp7),
      primeAxisFrequency, freqOp, LinearMap.prodMap_apply, LinearMap.id_apply, AlgEquiv.toLinearMap_apply,
      atTwoPrimeFourier_eigen R C u hu, Prod.smul_mk]
    by_cases hj : j.val = 0 <;> simp [hj]

private theorem monomialRows_eigen (a : PrimeAxisRow mₚ) :
    freqOp (R := R) C (primeAxisMonomialRows F a) =
      (u:R)^(primeAxisFrequency (hpos hp7) a).val • primeAxisMonomialRows F a := by
  cases a with
  | none =>
    simp [primeAxisMonomialRows, primeAxisOutputBasis, primeAxisFrequency, freqOp]
  | some a =>
    rcases a with ⟨i,j⟩
    have hb := F.equiv_basis (i,j)
    simp only [Basis.tensorProduct_apply'] at hb
    simpa [primeAxisMonomialRows, primeAxisOutputBasis, primeAxisFrequency, freqOp,
      primeAxisActiveBasis, hb] using F.eigen_basis (i,j)

/-- The remaining matrix changes between the two sets of coordinates at each frequency. -/
noncomputable def primeAxisResidual : Matrix (PrimeAxisRow mₚ) (PrimeAxisRow mₚ) R :=
  (primeAxisMonomialRows F).toMatrix (primeAxisOrbitRows (C := C) (u := u) hpu hm hu hs)

/-- Its inverse changes from the monomials back to the orbital Fourier vectors. -/
noncomputable def primeAxisResidualInv : Matrix (PrimeAxisRow mₚ) (PrimeAxisRow mₚ) R :=
  (primeAxisOrbitRows (C := C) (u := u) hpu hm hu hs).toMatrix (primeAxisMonomialRows F)

theorem primeAxisResidual_sparse (i j : PrimeAxisRow mₚ)
    (hne : primeAxisFrequency (hpos hp7) i ≠ primeAxisFrequency (hpos hp7) j) :
    primeAxisResidual F hpu hm hu hs i j = 0 :=
  eigenBasis_repr_eq_zero (freqOp (R := R) C) _ hs _ _ (monomialRows_eigen F) i hne.symm
    (orbitRows_eigen (C := C) (u := u) (hp7 := hp7) hpu hm hu hs j)

theorem primeAxisResidualInv_sparse (i j : PrimeAxisRow mₚ)
    (hne : primeAxisFrequency (hpos hp7) i ≠ primeAxisFrequency (hpos hp7) j) :
    primeAxisResidualInv F hpu hm hu hs i j = 0 :=
  eigenBasis_repr_eq_zero (freqOp (R := R) C) _ hs _ _ (orbitRows_eigen (C := C) (u := u) (hp7 := hp7) hpu hm hu hs) i hne.symm
    (monomialRows_eigen F j)

theorem primeAxisResidual_mul_inv :
    primeAxisResidual F hpu hm hu hs * primeAxisResidualInv F hpu hm hu hs = 1 := by
  simp [primeAxisResidual, primeAxisResidualInv, Basis.toMatrix_mul_toMatrix]

theorem primeAxisResidualInv_mul :
    primeAxisResidualInv F hpu hm hu hs * primeAxisResidual F hpu hm hu hs = 1 := by
  simp [primeAxisResidual, primeAxisResidualInv, Basis.toMatrix_mul_toMatrix]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
