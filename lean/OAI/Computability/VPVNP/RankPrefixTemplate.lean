import OAI.Computability.VPVNP.RankCursorPorts
import OAI.Computability.VPVNP.RankQueryStackGramInitialization

/-! # Supplying a variable row prefix to the determinant interpreter

The outer rank cursor and the Schur interpreter read the same dimension
from three places. All other startup stacks come from one reusable
matrix, field and reader template.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type} {p e : ℕ}

/-- Ports for a row-prefix rank scan whose Schur engine obtains Gram entries from the
underlying matrix reader. -/
abbrev PrefixPort (K : Type) := ScanPort (GramEngine.Aux K)

/-- Select the three ports that receive the variable row-prefix length, namely the row-count
stack, cursor input one, and Gram-engine register seven. -/
def prefixDynamic : PrefixPort K → Bool
  | .rows => true
  | .cursor (.isa (.reg i)) => decide (i = Registers.arg 1)
  | .engine (.aux (.inl (.inl (.reg i)))) => decide (i.val = 7)
  | _ => false

/-- Initial stacks for the rank of an n-row prefix with m columns, with the loop flag set, the
Gram engine idle, and the product-depth stack empty. -/
def prefixRawBank [DecidableEq K] (w v n m : ℕ) (c : SliceArithmetic.Vector p e)
    (base : Stacks K) : Stacks (PrefixPort K) :=
  Function.update
    (scanBank n (0 : Word w) (Registers.initial (Fin.ofNat _ m) (Fin.ofNat _ n) 0)
      [true] (idle (GramEngine.initial w v n m c base))) .depth []

/-- Substitution of the physical prefix-length word into the template gives
the complete initial bank, including the empty balanced-depth stack. -/
theorem prefixRawBank_eq [DecidableEq K] (w v n m : ℕ) (c : SliceArithmetic.Vector p e)
    (base : Stacks K) (h : PrefixPort K) : prefixRawBank w v n m c base h =
    if prefixDynamic h then digits w n else prefixRawBank w v 0 m c base h := by
  cases h with
  | rows | depth | scratch => rfl
  | cursor q =>
    cases q with
    | flag => rfl
    | isa a =>
      cases a with
      | pub i => exact i.elim0
      | persistent | work | logPort => rfl
      | reg i =>
        have h₃ : Registers.arg 1 ≠ Registers.arg 3 := by decide
        have h₂ : Registers.arg 1 ≠ Registers.arg 2 := by decide
        by_cases hi : i = Registers.arg 1
        · subst i
          change wordBits (Registers.initial (Fin.ofNat _ m) (Fin.ofNat _ n) 0 (Registers.arg 1)) = _
          simp [Registers.initial, prefixDynamic, h₃, h₂, digits]
        · change wordBits (Registers.initial (Fin.ofNat _ m) (Fin.ofNat _ n) 0 i) =
              if decide (i = Registers.arg 1) then digits w n else
                wordBits (Registers.initial (Fin.ofNat _ m) (0 : Word w) 0 i)
          simp [Registers.initial, hi, Function.update]
  | engine q =>
    cases q with
    | frame j => cases j <;> rfl
    | condition | result => rfl
    | aux a =>
      rcases a with (a | z) | extra
      · cases a with
        | pub i => exact i.elim0
        | persistent | work | logPort => rfl
        | reg i =>
          change wordBits (if i.val = 7 then (Fin.ofNat _ n : Word w) else 0) =
            if decide (i.val = 7) then digits w n else
              wordBits (if i.val = 7 then (Fin.ofNat _ 0 : Word w) else 0)
          by_cases hi : i.val = 7 <;> simp [hi, digits]
      · rfl
      · cases extra <;> rfl

theorem prefixRawBank_length [DecidableEq K] {w v n m A : ℕ} (c : SliceArithmetic.Vector p e)
    {ready : Stacks K → Prop} (base : Stacks K) (hr : ready base)
    (ha : ∀ s, ready s → ∀ i, (s i).length ≤ A) (hn : n < 2^w) (hm : m < 2^w)
    (i : PrefixPort K) : (prefixRawBank w v n m c base i).length ≤ w+v+e+e*v+A+1 := by
  have h := GramEngine.ready_length (GramEngine.initial_ready (c := c) (v := v) base hr hn hm) ha
  cases i with
  | cursor q =>
    exact (Registers.bank_length (0 : Word w) _ [true] q).trans (by simp; omega)
  | engine q =>
    cases q with
    | aux a => exact (h a).trans (Nat.le_succ _)
    | result | condition => exact Nat.zero_le _
    | frame j => cases j <;> exact Nat.zero_le _
  | rows => exact (length_digits w n).le.trans (by omega)
  | depth | scratch => exact Nat.zero_le _

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
