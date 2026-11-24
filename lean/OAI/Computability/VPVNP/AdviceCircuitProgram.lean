import Mathlib.Data.List.Defs

/-!
# Boolean circuit instructions for the coefficient-query interpreter

Each instruction reads unary addresses counted from the top of the valuation stack.
The newly computed gate value is prepended. A variable or a constant can be read
from the initial valuation stack, and all earlier gate values remain accessible.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace AdviceCircuit

/-- An advice instruction that computes NOT or AND from addresses counted from the top of the
current valuation stack. -/
inductive Instruction where
  | not (addr : ℕ)
  | and (left right : ℕ)
  deriving DecidableEq

/-- Encode an address as one true bit per valuation entry to skip followed by a false
terminator. -/
def unary (a : ℕ) : List Bool := List.replicate a true ++ [false]

/-- Encode a gate with a false tag for NOT or a true tag for AND, followed by one unary address
per operand. -/
def Instruction.encode : Instruction → List Bool
  | .not a => false :: unary a
  | .and a b => true :: (unary a ++ unary b)

/-- Concatenate the encodings of all instructions in execution order to form the circuit advice
stream. -/
def encode (p : List Instruction) : List Bool := p.flatMap Instruction.encode

/-- Evaluate one gate against a valuation list, returning none if any operand address falls
outside the list. -/
def Instruction.value (v : List Bool) : Instruction → Option Bool
  | .not a => v[a]?.map (!·)
  | .and a b => do return (← v[a]?) && (← v[b]?)

/-- Execute the instruction list, prepending each new gate value to the valuation used by the
remaining instructions. -/
def run : List Instruction → List Bool → Option (List Bool)
  | [], v => some v
  | a :: p, v => do run p ((← a.value v) :: v)

@[simp] theorem run_nil (v : List Bool) : run [] v = some v := rfl

theorem run_cons {a : Instruction} {p : List Instruction} {v : List Bool} {b : Bool}
    (h : a.value v = some b) : run (a :: p) v = run p (b :: v) := by simp [run, h]

theorem run_append (p q : List Instruction) (v : List Bool) :
    run (p ++ q) v = (run p v).bind (run q) := by
  induction p generalizing v with
  | nil => rfl
  | cons a p ih =>
    cases h : a.value v <;> simp [run, h, ih]

theorem length_run {p : List Instruction} {v u : List Bool} (hu : run p v = some u) :
    u.length = p.length + v.length := by
  induction p generalizing v with
  | nil => simpa [run] using congrArg (Option.map List.length) hu.symm
  | cons a p ih =>
    cases h : a.value v with
    | none => simp [run, h] at hu
    | some b =>
      rw [run_cons h] at hu
      have hh := ih hu
      simp only [List.length_cons] at *
      omega

end AdviceCircuit

end VPVNP
end Computability
end OAI
