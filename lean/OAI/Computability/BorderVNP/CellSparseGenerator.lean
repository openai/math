import OAI.Computability.BorderVNP.CellBytecode
import Mathlib.Data.Nat.Bits

/-! # Private bounded-loop generators for sparse cell records

Loop variables are lexical indices, with index zero for the innermost copy or lane.
The generator describes private instructions before their reads are expanded into unary.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro (Op)

/-- An integer expression over constants and enclosing loop counters. -/
inductive NatExpr where
  | lit (n : ℕ)
  | index (depth : ℕ)
  | add (a b : NatExpr)
  | mul (a b : NatExpr)
  | sub (a b : NatExpr)
  deriving DecidableEq

/-- Evaluate a generator address without reading any nondeterministic wire bits. -/
def NatExpr.eval (env : List ℕ) : NatExpr → ℕ
  | .lit n => n
  | .index i => env.getD i 0
  | .add a b => a.eval env + b.eval env
  | .mul a b => a.eval env * b.eval env
  | .sub a b => a.eval env - b.eval env

/-- Instructions in the private generator, with lexical bounds and addresses.
`bit` extracts a bit of an index or a parameter at expansion time. `fixed` emits
one instruction without inspecting the value bank. -/
inductive Stmt where
  | nil
  | fixed (op : Op)
  | read (address : NatExpr)
  | bit (value index : NatExpr)
  | seq (left right : Stmt)
  | loop (bound : NatExpr) (body : Stmt)
  | ifEq (a b : NatExpr) (yes no : Stmt)
  deriving DecidableEq

/-- Privately unfold the loops, emitting the elementary stack instructions in order. -/
def Stmt.expand (s : Stmt) (env : List ℕ) : List Op :=
  match s with
  | .nil => []
  | .fixed op => [op]
  | .read a => [.read (a.eval env)]
  | .bit v i => [.literal ((v.eval env).testBit (i.eval env))]
  | .seq a b => a.expand env ++ b.expand env
  | .loop bound body => (List.range (bound.eval env)).flatMap fun i => body.expand (i :: env)
  | .ifEq a b yes no => if a.eval env = b.eval env then yes.expand env else no.expand env

/-- Concatenate generator fragments without duplicating either branch of an iteration. -/
def sequence (fs : List Stmt) : Stmt := fs.foldr Stmt.seq .nil

/-- Concatenation emits each component's working bytecode consecutively. -/
theorem expand_sequence (fs : List Stmt) (env : List ℕ) :
    (sequence fs).expand env = fs.flatMap (fun s => s.expand env) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [sequence, Stmt.expand] at ih ⊢; exact ih

/-- Prefix framing used for natural-number fields in private generator literals. -/
def encodeNat (n : ℕ) : List Bool := n.bits.flatMap (fun b => [true, b]) ++ [false]

/-- Binary-tagged prefix representation of an address expression. -/
def NatExpr.code : NatExpr → List Bool
  | .lit n => [false, false, false] ++ encodeNat n
  | .index d => [false, false, true] ++ encodeNat d
  | .add a b => [false, true, false] ++ a.code ++ b.code
  | .mul a b => [false, true, true] ++ a.code ++ b.code
  | .sub a b => [true, false, false] ++ a.code ++ b.code

/-- Compact command encoding. A loop stores its body only once and uses binary
integer fields in read offsets, including offsets of fixed read instructions. -/
def Stmt.code : Stmt → List Bool
  | .nil => [false, false, false]
  | .fixed (.read k) => [false, true, false] ++ (NatExpr.lit k).code
  | .fixed op => [false, false, true] ++ op.bits
  | .read a => [false, true, false] ++ a.code
  | .bit a b => [false, true, true] ++ a.code ++ b.code
  | .seq a b => [true, false, false] ++ a.code ++ b.code
  | .loop n body => [true, false, true] ++ n.code ++ body.code
  | .ifEq a b yes no => [true, true, false] ++ a.code ++ b.code ++ yes.code ++ no.code

end CellSparse

end BorderVNP
end Computability
end OAI
