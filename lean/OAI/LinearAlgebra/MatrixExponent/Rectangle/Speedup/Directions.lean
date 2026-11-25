import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Fin.VecNotation

/-! # The one-sided coordinate derivatives of an exponent -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Set

def vary (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) (t : ℝ) : ℝ :=
  ![L (a + t) b c, L a (b + t) c, L a b (c + t)] e

def partialRight (L : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) (e : Fin 3) : ℝ :=
  derivWithin (vary L a b c e) (Ici 0) 0

end OAI.LinearAlgebra.MatrixExponent.Rectangle
