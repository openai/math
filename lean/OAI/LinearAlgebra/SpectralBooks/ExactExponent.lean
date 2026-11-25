import OAI.LinearAlgebra.MatrixExponent.Integral.RingFormula
import OAI.LinearAlgebra.SpectralBooks.DualExponent
import OAI.LinearAlgebra.SpectralBooks.RectangularCircuitModel
import OAI.LinearAlgebra.SpectralBooks.SquareRankModel

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- The square matrix multiplication exponent over every field. -/
theorem square_exponent (F : Type*) [Field F] : formalOmega F 1 1 1 = (9 : ℝ) / 4 :=
  (formalOmega_square_eq_omega F).trans (MatrixExponent.omega_eq F)

/-- The dual matrix multiplication exponent over every field. -/
theorem dual_exponent (F : Type*) [Field F] : formalAlpha F = (1 : ℝ) / 2 := by
  obtain ⟨hs, hr⟩ := MatrixExponent.omega_eq_and_rigidity F
  calc
    formalAlpha F = MatrixExponent.Rectangle.dual F 1 1 := by
      unfold formalAlpha dualExponent MatrixExponent.Rectangle.dual
      congr 1
      ext t
      simp only [Set.mem_ofPred_eq, min_self, one_add_one_eq_two]
      apply and_congr_right
      intro ht
      rw [formalOmega_eq_integral, MatrixExponent.Integral.agreement F ht.1 zero_le_one zero_le_one,
        MatrixExponent.Rectangle.cycle F ht.1 zero_le_one zero_le_one]
    _ = (1 : ℝ) / 2 := MatrixExponent.Rectangle.dual_square hr hs

private theorem benchmark_sorted (a b c : ℝ) :
    MatrixExponent.Rectangle.U c b a =
      let x := max a (max b c)
      let z := min a (min b c)
      let y := a + b + c - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  let x := max a (max b c)
  let z := min a (min b c)
  let y := a + b + c - x - z
  change MatrixExponent.Rectangle.U c b a = MatrixExponent.Rectangle.benchmark x y z
  have sorted (u v w : ℝ) (hw : w = z)
      (huv : (u = x ∧ v = y) ∨ (u = y ∧ v = x)) :
      MatrixExponent.Rectangle.benchmark u v w = MatrixExponent.Rectangle.benchmark x y z := by
    rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> rw [hu, hv, hw]
    simp only [MatrixExponent.Rectangle.benchmark, add_comm y x, mul_comm y x,
      show 4 * y * x = 4 * x * y by ring]
  unfold MatrixExponent.Rectangle.U
  split_ifs <;> apply sorted <;> dsimp only [x, y, z] <;> grind

/-- The exact rectangular exponent with the nonnegative parts of the weights sorted
in descending order. On coordinate planes the correction term is zero. -/
theorem rectangular_exponent (F : Type*) [Field F] (a b c : ℝ) :
    formalOmega F a b c =
      let A := max a 0
      let B := max b 0
      let C := max c 0
      let x := max A (max B C)
      let z := min A (min B C)
      let y := A + B + C - x - z
      x + y + (max ((x + y) * z - x * y) 0) ^ 2 / (4 * x * y * z) := by
  rw [formalOmega_max_zero F a b c, formalOmega_eq_integral,
    MatrixExponent.Integral.exponent_eq F (le_max_right ..) (le_max_right ..) (le_max_right ..)]
  exact benchmark_sorted _ _ _

end SpectralBooks
end LinearAlgebra
end OAI
