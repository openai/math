import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointGridWords
import OAI.LinearAlgebra.FiniteFourier.FiberSynchronization

/-! # Split-endpoint words with occupied Fourier workspace

The quadratic transform and the power scalings can run together in the data registers.
The remaining grid consists of two independent copies of each occupied binomial Fourier
word per axis, with the same workspace-to-data ratio as a single copy.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix
open scoped Kronecker

variable {A : Type*} [CommRing A]

private theorem occupied_kronecker_one_left {I J W : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
    {F : Matrix I I A} {d : ℕ} (h : OccupiedWord W d F) :
    OccupiedWord (W × J) d ((1 : Matrix J J A) ⊗ₖ F) := by
  have hb := h.parallelOccupiedCopies (J := J) (V := W × J) le_rfl
  have hh := OccupiedWord.relabel hb (Equiv.prodComm I J)
  convert hh using 1
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases he : i = k <;> simp [he, one_apply, kroneckerMap_apply, blockDiagonal_apply]

variable {σ : Type} [Fintype σ] [DecidableEq σ]

private theorem occupied_split_fourier_grid (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    {F : ∀ i, Matrix (Fin (m i)) (Fin (m i)) A} {D : ℕ}
    (hF : ∀ i, OccupiedWord (Fin (13*m i)) D (F i)) :
    OccupiedWord (Fin (Fintype.card (Address m)*13)) (243*D)
      (gridTensor fun i => (1 : Matrix (Fin 2) (Fin 2) A) ⊗ₖ F i) := by
  apply occupiedWord_gridTensor (c := 14) (W := fun i => Fin (13*m i) × Fin 2) (by decide)
  · intro i
    simp only [Fintype.card_prod, Fintype.card_fin]
    have := hm i
    omega
  · intro i
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · exact fun i => occupied_kronecker_one_left (hF i)

variable [Finite (MaximalSpectrum A)]

private theorem word_split_quadratic_scale (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (Q : σ → Matrix (Fin 2) (Fin 2) A) (hQ : ∀ i, IsUnit (Q i))
    (w : σ → Aˣ) :
    LayerWord 37 (gridTensor fun i => Q i ⊗ₖ diagonal (fun j : Fin (m i) => (w i : A)^j.val)) := by
  apply layerWord_grid
  intro i
  apply layerWord_tensor
  · simpa using layerWord_semilocal_isUnit hs (Q i) (hQ i)
  · exact (layerWord_of_layer (layerMatrix_diagonal_units (fun j : Fin (m i) =>
      (w i).isUnit.pow j.val))).pad (by decide)

/-- Evaluation with occupied Fourier words on the binomial axes. -/
theorem occupiedWord_evaluationGrid (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ) (hm : ∀ i, 0 < m i)
    (hu : ∀ i, Pairwise fun j k => IsUnit (u i j - u i k)) {D : ℕ}
    (hF : ∀ i, OccupiedWord (Fin (13*m i)) D (dftMatrix (m i) (ζ i : A))) :
    OccupiedWord (Fin (Fintype.card (Address m)*13)) (243*D+37)
      (evaluationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i))) := by
  have hq := word_split_quadratic_scale hs m _ (fun i => unit_quadratic_vandermonde _ (hu i)) w
  have hf := occupied_split_fourier_grid m hm hF
  simpa only [evaluationGrid, vandermonde_scaledNodes, ← gridTensor_mul,
    ← mul_kronecker_mul, Matrix.one_mul] using OccupiedWord.mul hf hq.occupied

/-- Interpolation reverses evaluation, using the same occupied registers. -/
theorem occupiedWord_interpolationGrid (hs : ∀ x : A, ∃ t, IsUnit t ∧ IsUnit (x-t))
    (m : σ → ℕ) (u : σ → Fin 2 → A) (w ζ : σ → Aˣ) (hm : ∀ i, 0 < m i)
    (hu : ∀ i, Pairwise fun j k => IsUnit (u i j - u i k)) {D : ℕ}
    (hF : ∀ i, OccupiedWord (Fin (13*m i)) D (dftMatrix (m i) (ζ i : A))⁻¹) :
    OccupiedWord (Fin (Fintype.card (Address m)*13)) (243*D+37)
      (interpolationGrid m u (fun i => scaledNodes (m i) (w i) (ζ i))) := by
  have hq := word_split_quadratic_scale hs m _
    (fun i => isUnit_nonsing_inv_iff.mpr (unit_quadratic_vandermonde _ (hu i)))
    (fun i => (w i)⁻¹)
  have hf := occupied_split_fourier_grid m hm hF
  rw [Nat.add_comm]
  simpa only [interpolationGrid, inv_vandermonde_scaledNodes, ← gridTensor_mul,
    ← mul_kronecker_mul, Matrix.mul_one] using OccupiedWord.mul hq.occupied hf

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
