import OAI.Computability.NearSquareRoot.CommonAlphabetAlignRun
import OAI.Computability.NearSquareRoot.CommonAlphabetAlignRewind
import OAI.Computability.NearSquareRoot.ShortWordStack

/-! # Returning a halted output head to zero on the same public alphabet -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Align
open IntegerMultiplication TM
variable {A Q I : Type} [DecidableEq A] [DecidableEq I]

/-- One setup step, one halt-dispatch step, one leftward step of the folded counter
per cell of distance, and one final step erasing the sentinel. -/
theorem complete (out : I) (blank marker : A) (hne : blank ≠ marker) (m : Rule A Q I)
    {x y : Config A Q I} {n : ℕ} (zero : (x.tape out).pos=0)
    (run : Trace (advance m) x n y) (halt : advance m y=none) :
    Trace (advance (rule out blank marker x.pc m)) (initial x blank)
      (n+(y.tape out).pos.natAbs+3) (final out blank y) := by
  obtain ⟨neg,sign,first⟩ := checkpoint out blank marker hne m zero run
  have last := (Trace.single (dispatch out blank marker x.pc m neg y halt sign)).trans
    (unwind out blank marker x.pc m hne neg y (y.tape out).pos.natAbs)
  convert first.trans last using 1
  omega

theorem time {G P J : Type} {m : Rule G P J} {x y : Config G P J} {n : ℕ}
    (out : J) (zero : (x.tape out).pos=0) (run : Trace (advance m) x n y) :
    n+(y.tape out).pos.natAbs+3 ≤ 2*n+3 := by
  obtain ⟨lo,hi⟩ := head_excursion run out
  rw [zero] at lo hi
  have h : (y.tape out).pos.natAbs ≤ n := by
    have h' : ((y.tape out).pos.natAbs : ℤ) ≤ n := by
      rw [Int.natCast_natAbs,abs_le]
      constructor <;> omega
    exact_mod_cast h'
  omega

theorem loaded {B P J : Type} [DecidableEq J] (out : J) (blank : B)
    (x : Config B P J) (z : List B) (data : whole blank z (x.tape out)) :
    ((final out blank x).tape (some out)) = Tape.loaded blank z := by
  change outputAt out x 0 out = _
  simp only [outputAt,↓reduceIte]
  rw [show (x.tape out).absolute = (Tape.loaded blank z).absolute from data]
  exact asAtHead (Tape.loaded blank z)

end CommonAlphabet.Align

end NearSquareRoot
end Computability
end OAI
