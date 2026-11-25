import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoPrimeResidual

/-! # Factoring the full prime-axis coordinate changes

Index the cyclic powers by signed orbits. The forward conversion applies
two normalized orbit DFTs followed by changes of basis within frequencies.
The inverse conversion first inverts the frequency blocks and then
synthesizes the negative-sign Fourier vectors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Module Matrix Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} [Fact p.Prime]
  {C : PrimeAxisCosets p} {u : Rˣ} {hp7 : 7 ≤ p}

local notation "mₚ" => ((p-1)/2 : ℕ)
local notation "Aₚ" => AdjoinRoot (cyclotomic p R)

variable (F : AtTwoPrimeFactor R C u hp7) (hpu : IsUnit (p:R))
  (hm : IsUnit (((p-1)/2 : ℕ) : R)) (hu : u^((p-1)/2) = 1)
  (hs : ∀ i j : Fin ((p-1)/2), i ≠ j → IsUnit ((u:R)^i.val - (u:R)^j.val))

/-- Match output row indices with the signed monomial addresses of the source. -/
noncomputable def primeAxisAddress (C : PrimeAxisCosets p) : PrimeAxisRow mₚ ≃ ZMod p :=
  (primeAxisSignedIndex mₚ).trans (atTwoRawIndex C)

private noncomputable def cyclicRows (C : PrimeAxisCosets p) : Basis (PrimeAxisRow mₚ) R (R × Aₚ) :=
  ((atTwoRawMonomialBasis R C).map (primeCyclicCRT R p hpu).toLinearEquiv).reindex
    (primeAxisSignedIndex mₚ).symm

private theorem orbital_analysis :
    (primeAxisOrbitRows (C := C) hpu hm hu hs).toMatrix (cyclicRows hpu C) =
      (atTwoRawTransform ((↑hm.unit⁻¹:R) • dftMatrix mₚ (u:R))).submatrix
        (primeAxisSignedIndex mₚ) (primeAxisSignedIndex mₚ) := by
  rw [← atTwoRawFourier_analysis R C u hm hu hs]
  ext i j
  simp [primeAxisOrbitRows, cyclicRows, Basis.toMatrix_apply, Basis.map_repr]

private theorem orbital_synthesis :
    (cyclicRows hpu C).toMatrix (primeAxisOrbitRows (C := C) hpu hm hu hs) =
      (atTwoRawTransform (dftMatrix mₚ (↑u⁻¹:R))).submatrix
        (primeAxisSignedIndex mₚ) (primeAxisSignedIndex mₚ) := by
  rw [← atTwoRawFourier_synthesis R C u hm hu hs]
  ext i j
  simp [primeAxisOrbitRows, cyclicRows, Basis.toMatrix_apply, Basis.map_repr]

/-- The forward prime-axis conversion is orbit analysis followed by the residual blocks. -/
theorem primeAxisMatrix_decomposition :
    (primeAxisMatrix (by omega : 0 < mₚ) (primeAxisProductEquiv (primeCyclicCRT R p hpu) F.equiv)).submatrix
        id (primeAxisAddress C) =
      primeAxisResidual F hpu hm hu hs *
        (atTwoRawTransform ((↑hm.unit⁻¹:R) • dftMatrix mₚ (u:R))).submatrix
          (primeAxisSignedIndex mₚ) (primeAxisSignedIndex mₚ) := by
  rw [← orbital_analysis (C := C) hpu hm hu hs, primeAxisResidual, Basis.toMatrix_mul_toMatrix]
  ext i j
  simp [primeAxisMatrix, primeAxisMonomialRows, cyclicRows, primeAxisProductEquiv,
    primeAxisAddress, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
    Basis.map_repr, Matrix.submatrix]

/-- The inverse prime-axis conversion is inverse residual blocks followed by synthesis. -/
theorem primeAxisInvMatrix_decomposition :
    (primeAxisInvMatrix (by omega : 0 < mₚ) (primeAxisProductEquiv (primeCyclicCRT R p hpu) F.equiv)).submatrix
        (primeAxisAddress C) id =
      (atTwoRawTransform (dftMatrix mₚ (↑u⁻¹:R))).submatrix
          (primeAxisSignedIndex mₚ) (primeAxisSignedIndex mₚ) *
        primeAxisResidualInv F hpu hm hu hs := by
  rw [← orbital_synthesis (C := C) hpu hm hu hs, primeAxisResidualInv, Basis.toMatrix_mul_toMatrix]
  ext i j
  simp [primeAxisInvMatrix, primeAxisMonomialRows, cyclicRows, primeAxisProductEquiv,
    primeAxisAddress, LinearMap.toMatrix_apply, Basis.toMatrix_apply,
    Basis.map_repr, Matrix.submatrix, atTwoRawMonomialBasis]

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
