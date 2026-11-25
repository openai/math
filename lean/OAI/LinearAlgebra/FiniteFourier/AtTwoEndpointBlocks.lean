import OAI.LinearAlgebra.FiniteFourier.AtTwoEndpointWords
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Parallel elimination on the fibers of an arbitrary finite partition -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

/-- Invertible blocks supported on fibers of size at most `b` have a common
word of depth `9*b²+1`, independently of the number of fibers. -/
theorem layerWord_semilocal_blocks {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)]
    (hs : ∀ x : R, ∃ t, IsUnit t ∧ IsUnit (x - t))
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (f : I → J) {b : ℕ} (M : Matrix I I R) (hM : IsUnit M)
    (hzero : ∀ i i', f i ≠ f i' → M i i' = 0)
    (hcard : ∀ j, Fintype.card {i // f i = j} ≤ b) :
    LayerWord (9 * b ^ 2 + 1) M := by
  classical
  let B := M.toSquareBlock f
  have hu (j : J) : IsUnit (B j) := by
    apply (isUnit_iff_isUnit_det _).mpr
    have h := (isUnit_iff_isUnit_det M).mp hM
    rw [M.twoBlockTriangular_det (fun i => f i = j)
      (fun i hi k hk => hzero i k (fun he => hi (he.trans hk)))] at h
    exact isUnit_of_mul_isUnit_left h
  have hw (j : J) : LayerWord (9*b^2+1) (B j) := by
    apply (layerWord_semilocal_isUnit hs (B j) (hu j)).pad
    gcongr
    exact hcard j
  let e := Equiv.sigmaFiberEquiv f
  have hmat : M.submatrix e e = blockDiagonal' B := by
    ext ⟨j,i,hi⟩ ⟨j',i',hi'⟩
    by_cases h : j = j'
    · cases h
      rw [blockDiagonal'_apply_eq]
      rfl
    · rw [blockDiagonal'_apply_ne _ _ _ h]
      exact hzero i i' (hi ▸ hi' ▸ h)
  have h := (layerWord_blocks hw).relabel e
  rw [← hmat] at h
  simpa [Matrix.submatrix_submatrix] using h

end FiniteFourier
end LinearAlgebra
end OAI
