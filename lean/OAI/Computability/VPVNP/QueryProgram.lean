import Mathlib.Init

/-!
# Finite control for a binary query program

A read addresses one of the fixed payload bits and branches to another
control state. The clock counts payload queries. Halting consumes no query.
-/

namespace OAI
namespace Computability
namespace VPVNP

/-- One binary query action, either a Boolean halt or a payload-bit read with low and high
successor states. -/
inductive QueryStep (k : Nat) (Q : Type*) where
  | halt (accept : Bool)
  | read (i : Fin k) (low high : Q)

/-- A binary query program on `k` payload bits, specified by its initial state and the action
at each state. -/
structure QueryProgram (k : Nat) (Q : Type*) where
  /-- State from which execution of the query program begins. -/
  start : Q
  /-- Action prescribed at each query state, including the addressed bit and the two successors
  for a read. -/
  step : Q → QueryStep k Q

/-- Evaluate from a given state, spending one unit of fuel per bit read and rejecting a read
attempted at zero fuel. -/
def QueryProgram.eval {k : Nat} {Q : Type*} (p : QueryProgram k Q) (x : Fin k → Bool) :
    Nat → Q → Bool
  | 0, q =>
    match p.step q with
    | .halt b => b
    | .read _ _ _ => false
  | fuel + 1, q =>
    match p.step q with
    | .halt b => b
    | .read i low high => p.eval x fuel (if x i then high else low)

end VPVNP
end Computability
end OAI
