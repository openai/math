import OAI.Optimization.LinearProgramming.Compression.PowerBits

/-! A finite opcode stream for multiplying signed powers. Opcodes depend only on the
constructed exponent bits. Numerical bases remain separate scalar inputs. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

inductive PowerOp where
  | beginTerm | square | multiply | invert | commit
  deriving Repr, DecidableEq

def PowerOp.code : PowerOp → ℕ
  | .beginTerm => 0
  | .square => 1
  | .multiply => 2
  | .invert => 3
  | .commit => 4

structure PowerMem where
  base : ℚ
  power : ℚ
  product : ℚ
  remaining : List ℚ

def PowerMem.initial (bases : List ℚ) : PowerMem := ⟨0, 1, 1, bases⟩

def PowerMem.fits (B : ℕ) (m : PowerMem) : Prop :=
  ratBits m.base ≤ B ∧ ratBits m.power ≤ B ∧ ratBits m.product ≤ B ∧
  ∀ q ∈ m.remaining, ratBits q ≤ B

def PowerOp.step (op : PowerOp) (m : PowerMem) : Option PowerMem :=
  match op with
  | .beginTerm =>
    match m.remaining with
    | [] => none
    | q :: qs => some ⟨q, 1, m.product, qs⟩
  | .square => some {m with power := m.power * m.power}
  | .multiply => some {m with power := m.power * m.base}
  | .invert => if m.power = 0 then none else some {m with power := m.power⁻¹}
  | .commit => some {m with product := m.product * m.power}

inductive PowerRun (safe : PowerMem → Prop) : List PowerOp → PowerMem → PowerMem → Prop where
  | nil (m : PowerMem) (hm : safe m) : PowerRun safe [] m m
  | cons {op ops m n z} (hm : safe m) (hs : op.step m = some n)
      (hr : PowerRun safe ops n z) : PowerRun safe (op :: ops) m z

theorem PowerRun.append {safe : PowerMem → Prop} {xs ys : List PowerOp} {m n z : PowerMem}
    (hx : PowerRun safe xs m n) (hy : PowerRun safe ys n z) : PowerRun safe (xs ++ ys) m z := by
  induction hx with
  | nil => exact hy
  | cons hm hs _ ih => exact .cons hm hs (ih hy)

theorem PowerRun.safe_start {safe : PowerMem → Prop} {ops m z} (h : PowerRun safe ops m z) :
    safe m := by cases h <;> assumption

theorem PowerRun.safe_end {safe : PowerMem → Prop} {ops m z} (h : PowerRun safe ops m z) :
    safe z := by induction h <;> assumption

/-- Read the supplied bits from most to least significant. -/
def digitOps : List Bool → List PowerOp
  | [] => []
  | false :: bs => .square :: digitOps bs
  | true :: bs => .square :: .multiply :: digitOps bs

def termOps (e : ℤ) : List PowerOp :=
  .beginTerm :: (digitOps e.natAbs.bits.reverse ++
    (if e < 0 then [.invert, .commit] else [.commit]))

def productOps (exponents : List ℤ) : List PowerOp := exponents.flatMap termOps

end Compression
end LinearProgramming
end Optimization
end OAI
