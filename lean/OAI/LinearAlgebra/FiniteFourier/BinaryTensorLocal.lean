import OAI.LinearAlgebra.FiniteFourier.BinaryTensorWord
import OAI.LinearAlgebra.FiniteFourier.PrimeFourierSectors.FourierSectorGenerators
import OAI.LinearAlgebra.FiniteFourier.SynchronizedKernel

/-! # Synchronized local words for the protected binary shear -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix

variable {R : Type*} [CommRing R]

/-- Count every diagonal and every forward kernel call as a separate slot. -/
theorem ForwardBinaryWord.toKernelWord {p n : ℕ} {z : R} {C A : Matrix (Fin 2) (Fin 2) R}
    (hw : ForwardBinaryWord C n A) (hC : PrimeFourierSectors p z C) :
    KernelWord p z (2*n+1) A := by
  induction hw with
  | diagonal u v => exact KernelWord.diagonal p z ![(u : R), (v : R)]
  | @step n A u v _ ih =>
    have hd := KernelWord.diagonal p z ![(u : R), (v : R)]
    rw [show 2 * (n + 1) + 1 = 1 + 1 + (2*n+1) by omega]
    exact (hd.mul (KernelWord.fourier hC)).mul ih

private theorem hadamard_transvection_of_word {n : ℕ} {c : R}
    (hw : ForwardBinaryWord (compilerHadamard R) n !![1, c; 0, 1]) :
    KernelWord 2 (-1 : R) (2*n+1) (transvection (0 : Fin 2) 1 c) := by
  have hH : compilerHadamard R = dftMatrix 2 (-1 : R) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [compilerHadamard, dftMatrix]
  have hC : PrimeFourierSectors 2 (-1 : R) (compilerHadamard R) :=
    hH ▸ PrimeFourierSectors.full 2 (-1 : R)
  have ht : transvection (0 : Fin 2) 1 c = !![1, c; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection, Matrix.single]
  rw [ht]
  exact hw.toKernelWord hC

/-- Unit coefficients use three Fourier calls interleaved with four diagonal slots. -/
theorem protectedHadamard_unitTransvection_kernelWord [IsDomain R] {ζ : R}
    (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) (c : Rˣ) :
    KernelWord 2 (-1 : R) 7 (transvection (0 : Fin 2) 1 (c : R)) :=
  hadamard_transvection_of_word (protectedHadamard_unitShear_word hζ h₂ c)

/-- A shear with any coefficient in the protected semilocal domain uses
thirteen synchronized local slots, including the seven unit diagonals. -/
theorem protectedHadamard_transvection_kernelWord [IsDomain R] [Finite (MaximalSpectrum R)]
    {ζ : R} (hζ : IsPrimitiveRoot ζ 8) (h₂ : IsUnit (2 : R)) (c : R) :
    KernelWord 2 (-1 : R) 13 (transvection (0 : Fin 2) 1 c) :=
  hadamard_transvection_of_word (protectedHadamard_shear_word hζ h₂ c)

end FiniteFourier
end LinearAlgebra
end OAI
