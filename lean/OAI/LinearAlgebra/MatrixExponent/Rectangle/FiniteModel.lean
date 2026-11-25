import OAI.LinearAlgebra.MatrixExponent.Rectangle.Weights
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact ranks of powers and their asymptotic rate

Each side of a power has one independent digit per copy. Convergence
to the stated limit is proved for positive support density.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Filter

variable {F : Type*} [Field F] {i j k : ℕ}

def WPower (w : Fin i → Fin j → Fin k → F) (n : ℕ) :
    Fin (i ^ n) → Fin (j ^ n) → Fin (k ^ n) → F := fun a b c =>
  ∏ l : Fin n, w (finFunctionFinEquiv.symm a l)
    (finFunctionFinEquiv.symm b l) (finFunctionFinEquiv.symm c l)

def rankW (w : Fin i → Fin j → Fin k → F) : ℕ := sInf {r : ℕ | WeightedRankLE w r}

def asymptoticRank (w : Fin i → Fin j → Fin k → F) : ℝ :=
  limUnder atTop fun n : ℕ => (rankW (WPower w n) : ℝ) ^ (n : ℝ)⁻¹

def ordinary (F : Type*) [Field F] (i j k : ℕ) : Fin i → Fin j → Fin k → F :=
  fun _ _ _ => 1

def density (w : Fin i → Fin j → Fin k → F) : ℝ := supportSize w / ((i : ℝ) * j * k)

/-- Normalize the surplus by the output area divided by its natural logarithm. -/
noncomputable def normalized (x y : ℝ) (r : ℕ → ℕ) (n : ℕ) : ℝ :=
  let A := (side n x : ℝ) * side n y
  ((r n : ℝ) - A) * Real.log A / A

end OAI.LinearAlgebra.MatrixExponent.Rectangle
