import Mathlib.Basic.Finite.Prod

/-!
# Fixed deterministic finite-alphabet multitape model

We use bi-infinite one-dimensional tapes, finitely many via a `Finite` instance at the
application site. Step rule: simultaneous read, dependence only on reads and finite
control, halt or simultaneous write (choose the same symbol to skip writing)
and move left, stay or move right on each tape.
-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

/-- Exact n steps of a partial deterministic machine before consulting the next step. -/
inductive Trace {X : Type*} (step : X → Option X) : X → ℕ → X → Prop
  | nil (x) : Trace step x 0 x
  | cons {x y z n} : step x = some y → Trace step y n z → Trace step x (1+n) z

namespace Trace
variable {X : Type*} {step : X → Option X}

theorem single {x y} (h : step x = some y) : Trace step x 1 y :=
  .cons h (.nil _)

theorem trans {x y z n k} (h : Trace step x n y) (g : Trace step y k z) :
    Trace step x (n+k) z := by
  induction h with
  | nil => simpa using g
  | @cons x b c n s _ ih =>
    rw [add_assoc]
    exact .cons s (ih g)

end Trace

namespace TM

inductive Move
  | left
  | stay
  | right

namespace Move
def shift : Move → ℤ
  | left => -1
  | stay => 0
  | right => 1
end Move

/-- Tape seen relative to its head: position i is `pos + i` in absolute coordinates. -/
structure Tape (A : Type*) where
  pos : ℤ
  view : ℤ → A

namespace Tape
variable {A : Type*}

/-- Compute write followed by a move. -/
def apply (op : A × Move) (T : Tape A) : Tape A :=
  ⟨T.pos + op.2.shift,
    fun i => if i + op.2.shift = 0 then op.1 else T.view (i + op.2.shift)⟩

def absolute (T : Tape A) (i : ℤ) : A := T.view (i - T.pos)

theorem absolute_apply (op : A × Move) (T : Tape A) (i : ℤ) :
    absolute (apply op T) i = if i = T.pos then op.1 else T.absolute i := by
  simp only [absolute, apply]
  have h : i - (T.pos + op.2.shift) + op.2.shift = i - T.pos := by omega
  simp only [h, sub_eq_zero]

def loaded (blank : A) (s : List A) : Tape A :=
  ⟨0, fun i => match i with
    | .ofNat n => s[n]?.getD blank
    | .negSucc _ => blank⟩

end Tape

variable {A Q I : Type}

structure Config (A Q I : Type) where
  pc : Q
  tape : I → Tape A

abbrev Rule (A Q I : Type) := Q → (I → A) → Option (Q × (I → A × Move))

def advance (m : Rule A Q I) (x : Config A Q I) : Option (Config A Q I) :=
  (m x.pc (fun i => (x.tape i).view 0)).map fun (q, o) =>
    ⟨q, fun i => (x.tape i).apply (o i)⟩

/-- Absolute tape contents after writing exactly s and otherwise blank (independent of
current head position). -/
def whole (blank : A) (s : List A) (T : Tape A) : Prop :=
  T.absolute = (Tape.loaded blank s).absolute

end TM

end IntegerMultiplication
end Computability
end OAI
