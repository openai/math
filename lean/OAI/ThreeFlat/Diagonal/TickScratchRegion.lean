import Mathlib.Data.Nat.Notation

namespace OAI
/-! # Address regions for the physical diagonal tick -/

namespace ThreeFlat.Diagonal.TickWorkspace

/-- A region holds complete table streams and any polynomial-size headers.
The input and interpreter occupy the first region; all preprocessing writes
use positive region ordinals. -/
def stride (u : ℕ) := (2^(u^10))^4
def base (u i : ℕ) := (i+1)*stride u

end ThreeFlat.Diagonal.TickWorkspace

end OAI
