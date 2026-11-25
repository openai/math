import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.DeriveFintype

namespace OAI
/-! # An addressed table representation of bit tensor networks

Each cell reads three addressed bits and returns one coefficient. Input bits
are fixed, and each hidden bit is summed once regardless of its number of
uses. Constants pad the argument list of lower-arity cells.
-/

namespace ThreeFlat

inductive BitSource (internal pins : ℕ) where
  | hidden (i : Fin internal)
  | pin (i : Fin pins)
  | constant (b : Bool)
  deriving DecidableEq, Fintype

def BitSource.read {n p : ℕ} (hidden : Fin n → Bool) (pin : Fin p → Bool) :
    BitSource n p → Bool
  | .hidden i => hidden i
  | .pin i => pin i
  | .constant b => b

/-- The address and coefficient arrays of a bit network. Each coefficient row has eight entries. -/
structure BitNetwork (F : Type*) (p : ℕ) where
  internal : ℕ
  cells : ℕ
  source : Fin cells → Fin 3 → BitSource internal p
  table : Fin cells → (Fin 3 → Bool) → F

namespace BitNetwork

variable {F : Type*} {p : ℕ}

/-- The factor at one cell on a given assignment to all shared bits. -/
def factor (N : BitNetwork F p) (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (i : Fin N.cells) : F :=
  N.table i fun j => (N.source i j).read hidden pin

/-- The terminal weight on the branch that guesses precisely the given hidden bits. -/
def weight [CommMonoid F] (N : BitNetwork F p) (pin : Fin p → Bool)
    (hidden : Fin N.internal → Bool) : F :=
  ∏ i, N.factor pin hidden i

/-- The contraction with the prescribed input pins. -/
def eval [CommSemiring F] (N : BitNetwork F p) (pin : Fin p → Bool) : F :=
  ∑ hidden, N.weight pin hidden

end BitNetwork
end ThreeFlat

end OAI
