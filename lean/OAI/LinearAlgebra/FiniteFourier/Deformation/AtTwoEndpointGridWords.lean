import OAI.LinearAlgebra.FiniteFourier.AtTwoEndpointWords
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointSplit
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointTransport

/-! # Synchronized words for the split and transport endpoint matrices

The quadratic basis changes have bounded width. The binomial scaling costs one diagonal
layer. Thus the full grid adds only a constant number of slots to the common depth of
the one-axis Fourier words.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix
open scoped Kronecker

variable {A : Type*} [CommRing A] {σ : Type} [Fintype σ] [DecidableEq σ]
variable [Finite (MaximalSpectrum A)]

/-- The same constant bounds the word for either direction of the original endpoint. -/
theorem layerWord_transportGrid (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (x : σ → A) (y w : σ → Aˣ) : LayerWord 37 (transportGrid m x y w) := by
  apply layerWord_grid
  intro i
  apply layerWord_tensor
  · have h : IsUnit !![(1 : A), x i; 0, (y i : A)] := by
      rw [isUnit_iff_isUnit_det, det_fin_two_of]
      simp
    simpa using layerWord_semilocal_isUnit hs _ h
  · exact (layerWord_of_layer (layerMatrix_diagonal_units (fun j : Fin (m i) =>
      (w i).isUnit.pow j.val))).pad (by decide)

omit [Finite (MaximalSpectrum A)] in
theorem unit_quadratic_vandermonde (v : Fin 2 → A)
    (hu : Pairwise fun i j => IsUnit (v i - v j)) : IsUnit (vandermonde v) := by
  rw [isUnit_iff_isUnit_det, det_fin_two]
  simpa [vandermonde_apply] using hu (show (1 : Fin 2) ≠ 0 by decide)

omit [Finite (MaximalSpectrum A)] in
theorem inv_vandermonde_scaledNodes {m : ℕ} (w ζ : Aˣ) :
    (vandermonde (scaledNodes m w ζ))⁻¹ =
      diagonal (fun j : Fin m => (↑w⁻¹ : A)^j.val) * (dftMatrix m (ζ : A))⁻¹ := by
  rw [vandermonde_scaledNodes, Matrix.mul_inv_rev]
  congr 1
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal]
  simp [← mul_pow, ← diagonal_one]

/-- Exact-width axis Fourier words synchronize with the bounded quadratic evaluation
and with the unit scalings on all powers of the binomial generator. -/
theorem layerWord_evaluationGrid (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ)
    (hu : ∀ i, Pairwise fun j k => IsUnit (u i j - u i k)) {D : ℕ}
    (hF : ∀ i, LayerWord D (dftMatrix (m i) (ζ i : A))) :
    LayerWord (max 37 (D+1)) (evaluationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i))) := by
  apply layerWord_grid
  intro i
  apply layerWord_tensor
  · have h : LayerWord 37 (vandermonde (u i)) := by
      simpa using layerWord_semilocal_isUnit hs _ (unit_quadratic_vandermonde _ (hu i))
    exact h.pad (Nat.le_max_left ..)
  · rw [vandermonde_scaledNodes]
    apply LayerWord.pad (Nat.le_max_right ..)
    exact layerWord_mul (hF i) (layerWord_of_layer (layerMatrix_diagonal_units
      (fun j : Fin (m i) => (w i).isUnit.pow j.val)))

/-- Inverse evaluation has the same synchronized depth bound given the inverse-axis words. -/
theorem layerWord_interpolationGrid (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ)
    (hu : ∀ i, Pairwise fun j k => IsUnit (u i j - u i k)) {D : ℕ}
    (hF : ∀ i, LayerWord D (dftMatrix (m i) (ζ i : A))⁻¹) :
    LayerWord (max 37 (D+1)) (interpolationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i))) := by
  apply layerWord_grid
  intro i
  apply layerWord_tensor
  · have h : LayerWord 37 (vandermonde (u i))⁻¹ := by
      simpa using layerWord_semilocal_isUnit hs _
        (isUnit_nonsing_inv_iff.mpr (unit_quadratic_vandermonde _ (hu i)))
    exact h.pad (Nat.le_max_left ..)
  · rw [inv_vandermonde_scaledNodes]
    apply LayerWord.pad (Nat.le_max_right ..)
    rw [Nat.add_comm]
    exact layerWord_mul (layerWord_of_layer (layerMatrix_diagonal_units
      (fun j : Fin (m i) => ((w i)⁻¹).isUnit.pow j.val))) (hF i)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
