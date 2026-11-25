import OAI.LinearAlgebra.FiniteFourier.ProtectedBinaryWord

/-! # A three-Hadamard word over the protected binary coefficient ring -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R]

/-- Replacing each kernel by a diagonally scaled copy of another kernel
preserves the number of calls. -/
theorem ForwardBinaryWord.replaceKernel {C H A : Matrix (Fin 2) (Fin 2) R} {n : ℕ}
    (hw : ForwardBinaryWord C n A) (hC : ForwardBinaryWord H 1 C) :
    ForwardBinaryWord H n A := by
  induction hw with
  | diagonal u v => exact .diagonal u v
  | step u v _ ih =>
    have h := ((ForwardBinaryWord.diagonal (C := H) u v).mul hC).mul ih
    simpa only [Nat.zero_add, Nat.one_add] using h

private theorem protectedBinaryKernel_Hadamard_word {ζ : R} [IsDomain R]
    (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) :
    ForwardBinaryWord (compilerHadamard R) 1
      (protectedBinaryKernel (↑h₂.unit⁻¹ : R) (ζ^2)) := by
  let i := ζ^2
  let b := (↑h₂.unit⁻¹ : R)
  let a := (1+i)*b
  have hi : i^2 = -1 := by
    dsimp only [i]
    rw [← pow_mul]
    exact (IsPrimitiveRoot.pow (by decide : 0 < 8) hζ (show 8 = 4*2 by decide)).eq_neg_one_of_two_right
  obtain ⟨hroot, _, _, hs⟩ := compiler_eighthRoot_units hζ h₂
  have hu : IsUnit (-i) := (hroot.pow 2).neg
  have ha : IsUnit a := (show IsUnit (1 + i) by simpa [i, add_comm] using hs).mul
    (h₂.unit⁻¹).isUnit
  have he : protectedBinaryKernel b i = binaryUnitDiagonal ha.unit (ha.mul hu).unit *
      compilerHadamard R * binaryUnitDiagonal 1 hu.unit := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [binaryUnitDiagonal, protectedBinaryKernel, compilerHadamard, diagonal_mul, mul_diagonal, a]
    · linear_combination b * hi
    · linear_combination b * hi
    · linear_combination (1+i)*b * hi
  rw [show protectedBinaryKernel (↑h₂.unit⁻¹ : R) (ζ^2) = protectedBinaryKernel b i from rfl, he]
  exact .step _ _ (.diagonal _ _)

/-- The tensor compiler needs only forward calls to the positive-sign
binary Fourier matrix, with every interleaved scaling in the same ring. -/
theorem protectedHadamard_unitShear_word [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ 8)
    (h₂ : IsUnit (2 : R)) (t : Rˣ) :
    ForwardBinaryWord (compilerHadamard R) 3 !![1, (t : R); 0, 1] :=
  (protectedBinary_unitShear_word hζ h₂ t).replaceKernel (protectedBinaryKernel_Hadamard_word hζ h₂)

/-- In a protected semilocal domain an arbitrary shear coefficient needs
six positive-sign binary Fourier calls, uniformly in the coefficient. -/
theorem protectedHadamard_shear_word [IsDomain R] [Finite (MaximalSpectrum R)] {ζ : R}
    (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) (c : R) :
    ForwardBinaryWord (compilerHadamard R) 6 !![1, c; 0, 1] :=
  (protectedBinary_shear_word hζ h₂ c).replaceKernel (protectedBinaryKernel_Hadamard_word hζ h₂)

end FiniteFourier
end LinearAlgebra
end OAI
