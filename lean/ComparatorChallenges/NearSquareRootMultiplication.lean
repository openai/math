import Mathlib

/-! # Near-square-root logarithmic overhead for uniform integer multiplication

This independent statement uses the original P192 one-dimensional tape model.
The machine writes the full product, blanks the rest of its output tape, and
counts every distinct tape/address pair seen between initialization and halt.
-/

namespace OAI
namespace Computability

namespace IntegerMultiplication

/-- Exact n steps of a partial deterministic machine before consulting the next step. -/
inductive Trace {X : Type*} (step : X → Option X) : X → ℕ → X → Prop
  | nil (x) : Trace step x 0 x
  | cons {x y z n} : step x = some y → Trace step y n z → Trace step x (1+n) z

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

namespace IntegerMultiplication
def bitValue (s : List Bool) : ℕ := s.foldl (fun v b => 2*v + b.toNat) 0

end IntegerMultiplication

namespace NearSquareRoot

open IntegerMultiplication Filter
open scoped Topology

noncomputable def initialConfig {A Q I : Type} (start : Q) (inp : I) (bit : Bool → A)
    (sep blank : A) (x y : List Bool) : TM.Config A Q I := by
  classical
  exact ⟨start, fun i => TM.Tape.loaded blank
    (if i = inp then x.map bit ++ [sep] ++ y.map bit else [])⟩

def VisitsAtMost {A Q I : Type} (m : TM.Rule A Q I) (init : TM.Config A Q I)
    (steps cells : ℕ) : Prop :=
  ∃ visited : Finset (I × ℤ), visited.card ≤ cells ∧
    ∀ u : ℕ, u ≤ steps → ∀ c : TM.Config A Q I,
      Trace (TM.advance m) init u c → ∀ i : I, (i, (c.tape i).pos) ∈ visited

def haltingTimes {A Q I : Type} (m : TM.Rule A Q I)
    (load : List Bool → List Bool → TM.Config A Q I) (n : ℕ) : Set ℕ :=
  {t | ∃ x y, x.length = n ∧ y.length = n ∧ ∃ c,
    Trace (TM.advance m) (load x y) t c ∧ TM.advance m c = none}

/-- The maximum is over the actual halting times for all input pairs of length
`n`. A single excess exponent tends to zero for the same machine. -/
def UniformWorstCaseSpec : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q)
    (m : TM.Rule A Q I) (W : ℕ → ℕ) (S : ℕ),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    (∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, (W n : ℝ) ≤ n*(1+Real.log n)^((1 : ℝ) / (2 : ℕ) + δ n)) ∧
    (∀ n : ℕ, 0 < n → IsGreatest
      (haltingTimes m (initialConfig start inp bit sep blank) n) (W n)) ∧
    ∀ n : ℕ, 0 < n → ∀ x y : List Bool, x.length = n → y.length = n →
      let init := initialConfig start inp bit sep blank x y
      ∃ (t : ℕ) (finish : TM.Config A Q I) (z : List Bool),
        Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
        TM.whole blank (z.map bit) (finish.tape out) ∧ z.length = 2*n ∧
        bitValue z = bitValue x*bitValue y ∧ VisitsAtMost m init t (S*n)

theorem uniformIntegerMultiplication : UniformWorstCaseSpec := by
  sorry

end NearSquareRoot

namespace IntegerMultiplication

def Goal : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I)
    (start : Q) (m : TM.Rule A Q I)
    (C : ℕ),
    Function.Injective bit ∧ (∀ b, bit b ≠ blank ∧ bit b ≠ sep) ∧ sep ≠ blank ∧
    ∀ (n : ℕ), 0 < n → ∀ (x y : List Bool), x.length = n → y.length = n →
      ∃ (finish : TM.Config A Q I) (t : ℕ) (z : List Bool),
        (∃ initTape : I → TM.Tape A,
          initTape inp = TM.Tape.loaded blank (x.map bit ++ [sep] ++ y.map bit) ∧
          (∀ i, i ≠ inp → initTape i = TM.Tape.loaded blank []) ∧
          Trace (TM.advance m) { pc := start, tape := initTape } t finish) ∧
        TM.advance m finish = none ∧
        TM.whole blank (z.map bit) (finish.tape out) ∧
        z.length = 2*n ∧ bitValue z = bitValue x * bitValue y ∧
        (t : ℝ) ≤ C * (n : ℝ) *
          ((max 1 (Nat.clog 2 n) : ℕ) : ℝ) ^ ((1 : ℝ) - (2 : ℝ)⁻¹ ^ (182 : ℕ))

end IntegerMultiplication

/-- Fixed-tape integer multiplication below the classical logarithmic overhead. -/
theorem IntegerMultiplication.sub_nlogn_integer_multiplication : IntegerMultiplication.Goal := by
  sorry

end Computability
end OAI
