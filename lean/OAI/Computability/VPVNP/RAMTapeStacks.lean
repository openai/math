import OAI.Computability.VPVNP.RAMTape

/-!
# Elementary bit-stack instructions

A stack step changes at most one bit. All unbounded data belong to the stacks.
The named control can inspect a popped bit, including the empty-stack case.
Binary choices preserve their two branch slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- One finite-control instruction acting on a named stack bank. -/
inductive StackOp (K Q : Type*) where
  | push (k : K) (b : Bool) (next : Q)
  | pop (k : K) (next : Option Bool → Q)
  | goto (next : Q)
  | choose (low high : Q)
  | halt (accept : Bool)

/-- Instruction table for the bit-stack machine. -/
abbrev StackCode (K Q : Type*) := Q → StackOp K Q
/-- A bit list for each named stack, with its top at the head. -/
abbrev Stacks (K : Type*) := K → List Bool

variable {K Q : Type*} [DecidableEq K]

/-- A single deterministic, continuing instruction. The stored pop
continuation branches on its actual symbol. -/
inductive StackStep (code : StackCode K Q) : Q → Stacks K → Q → Stacks K → Prop
  | push {q s k b q'} (h : code q = .push k b q') :
      StackStep code q s q' (Function.update s k (b :: s k))
  | pop {q s k f} (h : code q = .pop k f) :
      StackStep code q s (f (s k).head?) (Function.update s k (s k).tail)
  | goto {q s q'} (h : code q = .goto q') : StackStep code q s q' s

/-- A deterministic sequence of exactly the given number of stack instructions. -/
inductive StackRuns (code : StackCode K Q) : ℕ → Q → Stacks K → Q → Stacks K → Prop
  | nil (q s) : StackRuns code 0 q s q s
  | cons {q s q' s' t u n} :
      StackStep code q s q' s' → StackRuns code n q' s' t u →
      StackRuns code (n + 1) q s t u

theorem StackRuns.trans {code : StackCode K Q} {a b q s q' s' t u}
    (h₁ : StackRuns code a q s q' s') (h₂ : StackRuns code b q' s' t u) :
    StackRuns code (a + b) q s t u := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih => simpa [Nat.succ_add] using StackRuns.cons hs (ih h₂)

/-- Accepting leaf multiplicity up to a stack instruction bound. -/
def stackPaths (code : StackCode K Q) : ℕ → Q → Stacks K → ℕ
  | 0, _, _ => 0
  | n + 1, q, s =>
    match code q with
    | .push k b q' => stackPaths code n q' (Function.update s k (b :: s k))
    | .pop k f => stackPaths code n (f (s k).head?) (Function.update s k (s k).tail)
    | .goto q' => stackPaths code n q' s
    | .choose low high => stackPaths code n low s + stackPaths code n high s
    | .halt b => b.toNat

theorem StackRuns.paths {code : StackCode K Q} {n q s t u}
    (h : StackRuns code n q s t u) (fuel : ℕ) :
    stackPaths code (fuel + n) q s = stackPaths code fuel t u := by
  induction h with
  | nil => rfl
  | cons hs _ ih => cases hs <;> simp_all [stackPaths]

/-- Every branch halts within the stated number of elementary instructions. -/
def StopsWithin (code : StackCode K Q) : ℕ → Q → Stacks K → Prop
  | 0, _, _ => False
  | n + 1, q, s =>
    match code q with
    | .push k b q' => StopsWithin code n q' (Function.update s k (b :: s k))
    | .pop k f => StopsWithin code n (f (s k).head?) (Function.update s k (s k).tail)
    | .goto q' => StopsWithin code n q' s
    | .choose low high => StopsWithin code n low s ∧ StopsWithin code n high s
    | .halt _ => True

end RAMTape

end VPVNP
end Computability
end OAI
