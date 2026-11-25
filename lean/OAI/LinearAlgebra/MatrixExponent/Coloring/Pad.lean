import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector

/-! # Extending a listed function by fixed points -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Coloring

def lowerHalf (h : ℕ) : B h ↪ B (h + 1) := Fin.castLEEmb (by rw [pow_succ]; omega)

def inflate (h : ℕ) (x : (Perm h).obj) (a : B (h + 1)) : B (h + 1) :=
  if ha : a.val < 2 ^ h then lowerHalf h (x ⟨a, ha⟩) else a

end OAI.LinearAlgebra.MatrixExponent.Routing
