import Mathlib.Data.Nat.Log

/-!
# Length-only operands of the live instruction table

The physical reader supplies the input length, address width, bucket size and
word width. Literals belong to the fixed program. Arithmetic is performed on
natural numbers before packing each output as a word. `Fits` checks every
intermediate result, including inputs to division and logarithms.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

/-- Public dimensions read by the live processor, comprising input length, site-address width,
bucket capacity, and RAM word width. -/
structure Geometry where
  /-- The physical input length in bits. -/
  n : ℕ
  /-- Bit width of the site address, so a group has two to this power sites. -/
  d : ℕ
  /-- The per-site RAM bucket capacity. -/
  H : ℕ
  /-- Bit width of a RAM word in this geometry. -/
  w : ℕ
  deriving DecidableEq, Repr

/-- Length expression formed from geometry parameters, literals, natural arithmetic, constant
division, binary logarithms, and powers of two. -/
inductive PublicExpr where
  | lit (v : ℕ)
  | n | d | H | w
  | add (a b : PublicExpr)
  | sub (a b : PublicExpr)
  | mul (a b : PublicExpr)
  | divConst (a : PublicExpr) (b : ℕ)
  | log2 (a : PublicExpr)
  | clog2 (a : PublicExpr)
  | pow2 (a : PublicExpr)
  deriving DecidableEq, Repr

namespace PublicExpr

/-- Evaluate a public expression in natural numbers, using truncated subtraction, floor
division, and the indicated floor or ceiling binary logarithm. -/
def eval (g : Geometry) : PublicExpr → ℕ
  | .lit v => v
  | .n => g.n
  | .d => g.d
  | .H => g.H
  | .w => g.w
  | .add a b => a.eval g + b.eval g
  | .sub a b => a.eval g - b.eval g
  | .mul a b => a.eval g * b.eval g
  | .divConst a b => a.eval g / b
  | .log2 a => Nat.log 2 (a.eval g)
  | .clog2 a => Nat.clog 2 (a.eval g)
  | .pow2 a => 2^(a.eval g)

/-- Bound on every intermediate register. The denominator of `divConst` is
also a program literal and must fit if division is performed with word arithmetic. -/
def Fits (g : Geometry) (bound : ℕ) (e : PublicExpr) : Prop :=
  e.eval g < bound ∧ match e with
  | .add a b | .sub a b | .mul a b => a.Fits g bound ∧ b.Fits g bound
  | .divConst a b => a.Fits g bound ∧ b < bound
  | .log2 a | .clog2 a | .pow2 a => a.Fits g bound
  | _ => True

/-- Fixed nonnegative integer powers use repeated multiplication. -/
def natPow (a : PublicExpr) : ℕ → PublicExpr
  | 0 => .lit 1
  | k+1 => .mul (natPow a k) a

@[simp] theorem eval_natPow (a : PublicExpr) (k : ℕ) (g : Geometry) :
    (a.natPow k).eval g = (a.eval g)^k := by
  induction k with
  | zero => simp [natPow, eval]
  | succ k ih => simp [natPow, eval, ih, Nat.pow_succ]

end PublicExpr
end LiveProgram

end VPVNP
end Computability
end OAI
