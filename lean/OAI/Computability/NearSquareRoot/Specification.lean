import OAI.Computability.IntegerMultiplication.Goal

/-!
# Uniform integer multiplication on fixed tapes

An independent specification of `thm:uniform-main` of *Near-square-root logarithmic
overhead for integer multiplication and exact transforms*. The step rule and
most-significant-first bit value are those of the earlier P192 formalization.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

open IntegerMultiplication

/-- All heads start at zero. Only the input tape contains symbols before execution. -/
noncomputable def initialConfig {A Q I : Type} (start : Q) (inp : I) (bit : Bool → A)
    (sep blank : A) (x y : List Bool) : TM.Config A Q I := by
  classical
  exact ⟨start, fun i => TM.Tape.loaded blank
    (if i = inp then x.map bit ++ [sep] ++ y.map bit else [])⟩

/-- A single finite set covers the tape/address pairs visited over the entire run,
including the initial and terminal head positions. Each physical cell is counted once. -/
def VisitsAtMost {A Q I : Type} (m : TM.Rule A Q I) (init : TM.Config A Q I)
    (steps cells : ℕ) : Prop :=
  ∃ visited : Finset (I × ℤ), visited.card ≤ cells ∧
    ∀ (u : ℕ), u ≤ steps → ∀ c : TM.Config A Q I,
      Trace (TM.advance m) init u c → ∀ i : I, (i, (c.tape i).pos) ∈ visited

/-- One machine, uniform over input lengths and exponents. On two arbitrary positive-length
`n`-bit strings, its real tape execution halts with the full `2*n`-bit product. A single
time majorant covers all inputs and a single linear space bound covers every tape. -/
def UniformMultiplicationSpec : Prop :=
  ∃ (A Q I : Type) (_ : Finite A) (_ : Finite Q) (_ : Finite I)
    (bit : Bool → A) (sep blank : A) (inp out : I) (start : Q)
    (m : TM.Rule A Q I) (T : ℕ → ℕ) (S : ℕ),
    Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (T n : ℝ) ≤ C * (n : ℝ) * (1 + Real.log n) ^ ((1 : ℝ) / 2 + ε)) ∧
    ∀ n : ℕ, 0 < n → ∀ x y : List Bool, x.length = n → y.length = n →
      let init := initialConfig start inp bit sep blank x y
      ∃ (t : ℕ) (finish : TM.Config A Q I) (z : List Bool),
        Trace (TM.advance m) init t finish ∧ TM.advance m finish = none ∧
        TM.whole blank (z.map bit) (finish.tape out) ∧
        z.length = 2 * n ∧ bitValue z = bitValue x * bitValue y ∧
        t ≤ T n ∧ VisitsAtMost m init t (S * n)

end NearSquareRoot
end Computability
end OAI
