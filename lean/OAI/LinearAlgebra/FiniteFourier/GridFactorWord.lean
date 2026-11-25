import OAI.LinearAlgebra.FiniteFourier.GridFactor
import OAI.LinearAlgebra.FiniteFourier.ToeplitzAdditiveWord
import OAI.LinearAlgebra.FiniteFourier.TriangularToeplitzWord

/-! # Geometric-grid and triangular Toeplitz words with occupied workspace

This is the one-factor lemma `up:toeplitz`. The data, partner array, two
cyclic convolution arrays, and both Fourier workspaces have an explicit
linear bound on the total register count.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {K : Type*} [Field K] {W : Type} [Fintype W] [DecidableEq W]
  {a b D : ℕ} {u : K}

/-- The single-factor word has depth linear in that of the auxiliary Fourier
transform and restores all five auxiliary arrays. -/
theorem gridFactor_word_of_fourier (ha : 0 < a) (hab : 2 * a ≤ b) (hu : IsPrimitiveRoot u b)
    (hF : OccupiedWord W D (geometricMatrix b u)) {A : Matrix (Fin a) (Fin a) K}
    (hA : GridFactor A) :
    OccupiedWord (Fin a ⊕ (Fin b ⊕ (Fin b ⊕ (W ⊕ W)))) (336*D+1463) A := by
  let : NeZero b := ⟨by omega⟩
  have hadd (c : ℤ → K) := additiveWord_toeplitz_of_fourier hab hu c hF
  obtain ⟨l, hl, hfac, rfl⟩ := hA.factor_list
  have h := occupiedWord_list_prod l (fun B hB ↦ gridFactor_word_of_additive ha (by omega)
    hu hadd (hfac B hB))
  apply LayerWord.pad _ h
  calc
    _ ≤ 7 * (6 * (8*D+34) + 5) := Nat.mul_le_mul_right _ hl
    _ = _ := by ring

omit [DecidableEq W] in
/-- The register count in `up:toeplitz`, when the working length is at
most six times the original side and the Fourier word uses at most `Cb` registers. -/
theorem gridFactor_word_registers (hba : b ≤ 6*a) (C : ℕ)
    (hW : b + Fintype.card W ≤ C*b) :
    Fintype.card (Fin a ⊕ (Fin a ⊕ (Fin b ⊕ (Fin b ⊕ (W ⊕ W))))) ≤ (12*C+2)*a := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  nlinarith only [hW, Nat.mul_le_mul_left C hba]

end FiniteFourier
end LinearAlgebra
end OAI
