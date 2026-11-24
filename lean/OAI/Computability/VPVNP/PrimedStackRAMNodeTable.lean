import OAI.Computability.VPVNP.PrimedStackRAMChildren
import OAI.Computability.VPVNP.PrimedCounterGuessFlow
import OAI.Computability.VPVNP.PrimedInputRAMFlowLinks

/-!
# Fixed word-RAM table for a node of the primed counter

After popping the top frame, the degree determines whether the next choice is
one word or three. The zero register for this test is initialized by the pop.
Each chooser uses registers 8 and 12 temporarily. On entry register 5 gives
the offset of the assembled input row. A standalone call can initialize it
from the persistent word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM
open PrimedCounter

variable {p r k w : ℕ}

/-- Turn a nonempty straight-line segment into structured code with exactly the
same number of instructions. -/
def straight (head : Op r k) : List (Op r k) → Flow r k
  | [] => .line head
  | op :: rest => .seq (.line head) (straight op rest)

theorem straight_length (head : Op r k) (rest : List (Op r k)) :
    (straight head rest).length = rest.length + 1 := by
  induction rest generalizing head with
  | nil => rfl
  | cons op rest ih => simp [straight, Flow.length, ih, Nat.add_comm]

/-- Every compiled occurrence of a nonempty straight-line sequence contains the
genuine opcode block used in its trace specification. -/
theorem contains_straight {M : Machine w p r k} (head : Op r k) (rest : List (Op r k))
    (lab : (straight head rest).Label → Fin p) (stop bad : Fin p)
    (h : Flow.Linked M (straight head rest) lab stop bad) :
    Contains M bad (lab (straight head rest).entry) (head :: rest) stop := by
  induction rest generalizing head with
  | nil =>
    exact .cons (h.atLabel ()) (.nil stop)
  | cons op rest ih =>
    have h₁ := h.seqLeft
    have h₂ := h.seqRight
    exact .cons (h₁.atLabel ()) (ih op _ h₂)

/-- A nonempty literal instruction list. -/
def lines (ops : List (Op r k)) (hn : ops ≠ []) : Flow r k :=
  straight (ops.head hn) ops.tail

theorem contains_lines {M : Machine w p r k} (ops : List (Op r k)) (hn : ops ≠ [])
    (lab : (lines ops hn).Label → Fin p) (stop bad : Fin p)
    (h : Flow.Linked M (lines ops hn) lab stop bad) :
    Contains M bad (lab (lines ops hn).entry) ops stop := by
  cases ops with
  | nil => contradiction
  | cons op ops => exact contains_straight op ops lab stop bad h

/-- Choices have distinct result, weight and zero registers. The scratch
registers are shared by the three successive invocations. -/
def guessRegs (dst : Fin 16) (h₈ : dst ≠ 8) (h₁₂ : dst ≠ 12) : Fin 3 ↪ Fin 16 where
  toFun := ![dst, 8, 12]
  inj' := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all

/-- Check and mark the chosen terminal position, read its input bit, compute the terminal
production index, and increment its count. -/
def leafLines : List Line := mark ++ leafBit ++ terminalIndex ++ increment

/-- Check that the chosen split is below the popped degree and both child states are below the
public state count. -/
def binaryChecks : List Line :=
  [.guardLt 2 0, .publicWord 11 7, .guardLt 3 11, .guardLt 4 11]

/-- Validate the binary choice, increment its production count, and push the right child
followed by the left for preorder traversal. -/
def binaryLines : List Line := binaryChecks ++ binaryIndex ++ increment ++ pushChildren

/-- Structured RAM code that guesses one terminal position and executes the leaf instruction
list. -/
def leafFlow : Flow 16 11 :=
  .seq (GuessWord.flow (guessRegs 2 (by decide) (by decide))) (lines leafLines (by decide))

/-- Structured RAM code that guesses a degree split and two child states before executing the
binary instruction list. -/
def binaryFlow : Flow 16 11 :=
  .seq (GuessWord.flow (guessRegs 2 (by decide) (by decide))) <|
  .seq (GuessWord.flow (guessRegs 3 (by decide) (by decide))) <|
  .seq (GuessWord.flow (guessRegs 4 (by decide) (by decide))) (lines binaryLines (by decide))

/-- Structured code for one preorder visit. Pop a frame and branch on whether its degree is
zero. -/
def nodeFlow : Flow 16 11 :=
  .seq (lines pop (by decide)) (.ifEq 0 12 leafFlow binaryFlow)

/-- Standalone instruction table for one node, initialized by copying the persistent state word
into register 5 as the input-row offset. -/
def nodeTemplate :=
  (Flow.seq (.line (.stateWord 5)) nodeFlow).template (some 5)

theorem node_template_fixed : nodeTemplate.literalWidth = 2 := rfl

/-- Exact number of elementary word instructions when a leaf succeeds, including
the one-word guess and the branch on the popped degree. -/
def leafWork (w : ℕ) := pop.length + 1 + (4*w+4) + leafLines.length

/-- The three fixed-width choices of an internal node. -/
def binaryWork (w : ℕ) := pop.length + 1 + 3*(4*w+4) + binaryLines.length

theorem leafWork_eq (w : ℕ) : leafWork w = 4*w + 50 := by unfold leafWork; change 13+1+(4*w+4)+32 = _; omega
theorem binaryWork_eq (w : ℕ) : binaryWork w = 12*w + 90 := by
  unfold binaryWork
  change 13+1+3*(4*w+4)+64 = _
  omega

end PrimedStackRAM

end VPVNP
end Computability
end OAI
