import OAI.Computability.NearSquareRoot.ScheduleChunkSetup
import OAI.Computability.NearSquareRoot.ShortWordCall

/-!
# Variable-split multiplication as a physical subroutine

The split exponent is an input of the program. The same program implements all
permitted shapes for a given digit multiplier, including ceiling division of
the operand width, preparation of each digit pair, shifted addition, and output
conversion.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkTask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop

/-- Time includes linear scans of the whole record at each digit pair, and a
single call to the short-word program on width `p.u`. -/
def budget (T : ℕ → ℕ) (p : Input) := (p.count+1) * (p.n+T p.u+1)

def answer (m : Operands → Word) (p : Input) := (p.state m p.count).2.reverse

theorem answer_spec (m : Operands → Word)
    (correct : ∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2)
    (p : Input) : (answer m p).length = 2*p.n ∧
      bitValue (answer m p) = bitValue p.x * bitValue p.y := by
  apply ChunkLoop.output_exact m _ _ rfl p.same p.positive
  intro x y hx hy
  exact correct ⟨(x,y),hx.trans hy.symm,hx.symm ▸ p.width_pos⟩

theorem product_task (m : Operands → Word) (T : ℕ → ℕ)
    (callee : Task (fun q : EqualWords => T q.val.1.length)
      (fun q => send q.val) (fun q => send (m q.val)))
    (width : ∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) :
    Task (budget T) (fun p => send (tally p.k,(p.x,p.y))) (fun p => send (answer m p)) := by
  have run := ((setup m).compose (loop m T callee width)).compose (emit m)
  apply run.bound 123
  intro p
  have h : 2*(60*(p.n+1)+T p.u)+1 ≤ 121*(p.n+T p.u+1) := by omega
  have inner := Nat.mul_le_mul_left (p.count+1) h
  have nle : p.n ≤ budget T p := (show p.n ≤ p.n+T p.u+1 by omega).trans
    (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  rw [show (p.count+1)*(121*(p.n+T p.u+1)) = 121 * budget T p by unfold budget; ring] at inner
  change p.n + (p.count+1)*(2*(60*(p.n+1)+T p.u)+1) + p.n + 1 ≤ _
  omega

/-- The stack program runs on finitely many genuine tapes, with actual
transition counts and restoration of the caller's other tape contents. -/
theorem product_on_tapes (m : Operands → Word) (T : ℕ → ℕ)
    (callee : Task (fun q : EqualWords => T q.val.1.length)
      (fun q => send q.val) (fun q => send (m q.val)))
    (width : ∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) :
    ShortWord.PhysicalTask (budget T) (fun p => send (tally p.k,(p.x,p.y)))
      (fun p => send (answer m p)) :=
  ShortWord.physicalTask (product_task m T callee width)

end ChunkTask

end NearSquareRoot
end Computability
end OAI
