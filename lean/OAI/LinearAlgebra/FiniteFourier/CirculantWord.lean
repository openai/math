import OAI.LinearAlgebra.FiniteFourier.Cyclic
import OAI.LinearAlgebra.FiniteFourier.DiagonalShear
import OAI.LinearAlgebra.FiniteFourier.ToeplitzCirculant

/-! # Circulant additions with occupied workspace

A normalized permutation of the Fourier frequencies implements the inverse
transform. Transforming both the source and target arrays permits an arbitrary
circulant addition using a single diagonal addition in frequency coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [Field K] {b : ℕ} [NeZero b] {u : K}
  {W : Type} [Fintype W] [DecidableEq W] {D : ℕ}

/-- The normalized negative-frequency matrix inverts geometric evaluation. -/
theorem inverseDftMatrix_mul_geometricMatrix (hu : IsPrimitiveRoot u b) :
    inverseDftMatrix b u * geometricMatrix b u = 1 := by
  have hF : geometricMatrix b u = dftMatrix b u := by
    ext i j
    exact geometricMatrix_apply b u i j
  rw [hF, ← reindex_fourierMatrix_zmod hu, ← reindex_inverseFourierMatrix_zmod hu]
  simp only [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv,
    inverse_mul_fourier _ _ (admissible_zmod hu), submatrix_one_equiv]

/-- One monomial layer normalizes and reverses the Fourier frequencies, leaving
the arbitrary contents of the borrowed registers unchanged. -/
theorem layerWord_inverseDftMatrix (hu : IsPrimitiveRoot u b)
    (hF : LayerWord D (fromBlocks (geometricMatrix b u) 0 0 (1 : Matrix W W K))) :
    LayerWord (1+D) (fromBlocks (inverseDftMatrix b u) 0 0 (1 : Matrix W W K)) := by
  let P : Matrix (Fin b) (Fin b) K := fun i j => if -i = j then (b : K)⁻¹ else 0
  have hP : LayerMatrix .monomial P :=
    LayerMatrix.monomial (Equiv.neg _) (fun _ => Units.mk0 _ (inv_ne_zero hu.neZero'.out))
  have hneg (i : Fin b) : u ^ (-i).val = (u ^ i.val)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_add, ← pow_mod_orderOf, ← hu.eq_orderOf, ← Fin.val_add, neg_add_cancel]
    simp
  have hPF : P * geometricMatrix b u = inverseDftMatrix b u := by
    ext i j
    rw [Matrix.mul_apply]
    simp [P, ite_mul, inverseDftMatrix, hu.neZero'.out]
    rw [pow_mul, hneg, inv_pow, ← pow_mul, Nat.mul_comm i.val j.val]
  simpa [fromBlocks_multiply, hPF] using
    layerWord_mul (layerWord_of_layer (hP.parallel (.id .monomial))) hF

private theorem layerWord_duplicate {K : Type*} [CommRing K] {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I K} (hA : LayerWord D (fromBlocks A 0 0 (1 : Matrix W W K))) :
    LayerWord D (fromBlocks (fromBlocks A 0 0 A) 0 0 (1 : Matrix (W ⊕ W) (W ⊕ W) K)) := by
  have h := (layerWord_parallel hA hA).relabel (Equiv.sumSumSumComm I W I W)
  convert h using 1
  ext x y
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y) <;>
    simp [submatrix, Equiv.sumSumSumComm, fromBlocks, one_apply]

/-- Conjugating diagonal additions by an occupied Fourier word adds a circulant
over the same coefficient ring. The inverse word may have a different depth. -/
theorem layerWord_circulantShear_of_inverse {K : Type*} [CommRing K] {u : K}
    {U : Matrix (Fin b) (Fin b) K} {E s : ℕ} (hu : u ^ b = 1)
    (hinv : U * geometricMatrix b u = 1) (v : Fin b → K)
    (hF : LayerWord D (fromBlocks (geometricMatrix b u) 0 0 (1 : Matrix W W K)))
    (hU : LayerWord E (fromBlocks U 0 0 (1 : Matrix W W K)))
    (hdiag : LayerWord s (fromBlocks 1 0 (diagonal ((geometricMatrix b u).mulVec v)) 1)) :
    LayerWord (E+s+D) (fromBlocks (fromBlocks 1 0 (circulant v) 1) 0 0
      (1 : Matrix (W ⊕ W) (W ⊕ W) K)) := by
  have hcir : U * diagonal ((geometricMatrix b u).mulVec v) * geometricMatrix b u = circulant v := by
    rw [Matrix.mul_assoc, ← fourier_mul_circulant_of_pow_eq_one hu v, ← Matrix.mul_assoc,
      hinv, Matrix.one_mul]
  have h := layerWord_mul
    (layerWord_mul (layerWord_duplicate hU) (layerWord_parallel hdiag (layerWord_one (I := W ⊕ W) s)))
    (layerWord_duplicate hF)
  simpa [fromBlocks_multiply, hinv, hcir] using h

/-- A diagonal addition in Fourier coordinates performs the circulant
addition on two arrays and restores both copies of the Fourier workspace. -/
theorem layerWord_circulantShear (hu : IsPrimitiveRoot u b) (v : Fin b → K)
    (hF : LayerWord D (fromBlocks (geometricMatrix b u) 0 0 (1 : Matrix W W K))) :
    LayerWord (2*D+4) (fromBlocks (fromBlocks 1 0 (circulant v) 1) 0 0
      (1 : Matrix (W ⊕ W) (W ⊕ W) K)) := by
  rw [show 2 * D + 4 = 1 + D + 3 + D by omega]
  exact layerWord_circulantShear_of_inverse hu.pow_eq_one (inverseDftMatrix_mul_geometricMatrix hu) v
    hF (layerWord_inverseDftMatrix hu hF) (layerWord_diagShear_lower _)

end FiniteFourier
end LinearAlgebra
end OAI
