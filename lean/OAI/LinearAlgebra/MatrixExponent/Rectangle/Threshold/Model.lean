import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel

/-! # Scaling the inner dimension at the harmonic threshold -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold

def width (n : ℕ) (x y a : ℝ) := ⌈a * (n : ℝ) ^ (x * y)⌉₊

def gain (b C u : ℝ) := Real.exp (-u) * (max (b + C * u) 0) ^ 2 / 4

def optimum (b C : ℝ) := if b ≤ 2 * C then C ^ 2 * Real.exp (b / C - 2) else b ^ 2 / 4

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold
