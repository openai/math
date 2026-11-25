import OAI.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! # Parameters of the finite border-rank inequality -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

def largest (i j k : ℕ) := max (i * j) (max (i * k) (j * k))

def value (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))

def slope (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.log (value F i j k) / Real.log ((i : ℝ) * j * k)

def Speedup.cStar : ℝ := sSup {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v}

end OAI.LinearAlgebra.MatrixExponent.Rectangle
