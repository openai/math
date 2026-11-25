import OAI.Computability.IntegerMultiplication.TMModel
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI
namespace Computability
namespace IntegerMultiplication

/-- Big endian value. -/
def bitValue (s : List Bool) : ℕ := s.foldl (fun v b => 2*v + b.toNat) 0

/-- Interface for multiplication. Definition only: declaration `Goal` is *not* a proof
of existence. Bounds stated as a uniform inequality with real-power factor (from n≥1,
equivalent at least as strong as eventual big O). Need output to be the canonical fixed
length by quantifying over the actual bits, checking length and numerical value. -/
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
end Computability
end OAI
