import OAI.Computability.IntegerMultiplication.Port.Lag
import Mathlib.Computability.Primrec.List

/-! # Finite integer syntax of the address operations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Opcode
open IntegerMultiplication.Port

abbrev Op := ℕ × (Bool × ℕ) × (Bool × ℕ) × Bool × ℕ × ℕ
abbrev Word := List Op
abbrev tag (o : Op) := o.1
abbrev target (o : Op) := o.2.1
abbrev source (o : Op) := o.2.2.1
abbrev negative (o : Op) := o.2.2.2.1
abbrev numerator (o : Op) := o.2.2.2.2.1
abbrev denominator (o : Op) := o.2.2.2.2.2

def eraseSpot {n : ℕ} (a : Spot (Fin n)) : Bool × ℕ := (a.1,a.2.val)

/-- Widths repeat their target in the unused source, and pivots carry the
unused coefficient zero. A missing gather coefficient is `+0/1`. -/
def encode {b n : ℕ} : Lag (Fin n) b → Op
  | .width a s => (0,eraseSpot a,eraseSpot a,s.neg,s.top.count,s.down.count)
  | .gather a k none => (1,eraseSpot a,eraseSpot k,false,0,1)
  | .gather a k (some s) => (1,eraseSpot a,eraseSpot k,s.neg,s.top.count,s.down.count)
  | .pivot h d => (2,(false,h.val),(true,d.val),false,0,1)

end Opcode

end NearSquareRoot
end Computability
end OAI
