import OAI.Computability.VPVNP.PairNodeChildImmediate
import OAI.Computability.VPVNP.PairVertexImage

/-!
# The child-argument block in the final vertex image

A single finite label space contains the slot initializer followed by the
parent header and the complete child loop. Its first sixteen private registers
serve the argument scan. The remaining registers form its private ordinal bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildCode.RegisterBank

open BurstRAM BurstRAM.PrivateRAM

variable {a p r w : ℕ}

/-- First interval of the combined labels. -/
def initPC (pc : Fin (2 ^ a + size a) → Fin p) (i : Fin (2 ^ a)) : Fin p :=
  pc (i.castAdd (size a))

/-- Second interval, using the child code's established label order. -/
def loc (pc : Fin (2 ^ a + size a) → Fin p) (j : Label a) : Fin p :=
  pc ((number a j).natAdd (2 ^ a))

/-- The first sixteen private registers of the child-argument segment, used to scan the
children and assemble their arguments. -/
def regs (prv : Fin (16 + 2 ^ a) ↪ Fin r) : Fin 16 ↪ Fin r := (Fin.castAddEmb (2 ^ a)).trans prv

/-- The final `2 ^ a` private registers of the child-argument segment, one for the ordinal of
each port slot. -/
def bank (prv : Fin (16 + 2 ^ a) ↪ Fin r) : Fin (2 ^ a) ↪ Fin r := (Fin.natAddEmb 16).trans prv

theorem bank_apart (prv : Fin (16 + 2 ^ a) ↪ Fin r) (i : Fin (2 ^ a)) (j : Fin 16) :
    bank prv i ≠ regs prv j := by
  apply prv.injective.ne
  intro eqn
  have hv := congrArg Fin.val eqn
  change 16 + i.val = j.val at hv
  have hj := j.isLt
  omega

/-- An eleven-operand segment with five-bit literals, ready to embed in a
shrink or refresh handler at an arbitrary supplied continuation. -/
def segment (a : ℕ) : VertexImage.Segment where
  count := 2 ^ a + size a
  privateRegs := 16 + 2 ^ a
  entry := (0 : Fin (2 ^ a)).castAdd (size a)
  row pc _ _ prv done := Fin.addCases
    (ChildBankInit.instruction (initPC pc) (bank prv) (headerPC (loc pc) 0))
    (fun i => instruction (loc pc) (regs prv) (bank prv) done ((number a).symm i))

/-- A host containing the segment satisfies the two code hypotheses of the
complete success and short-tape rejection theorems. -/
theorem segment_linked (M : Machine w p r 11) (pc : Fin (segment a).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
    (prv : Fin (segment a).privateRegs ↪ Fin r) (done : Fin p)
    (code : ∀ i, M.code (pc i) = ((segment a).row pc dfs saved prv done i).resize w) :
    ChildBankInit.Linked M (initPC pc) (bank prv) (headerPC (loc pc) 0) ∧
      ∀ j, M.code (loc pc j) = instruction (loc pc) (regs prv) (bank prv) done j := by
  constructor
  · intro i
    apply (code (i.castAdd (size a))).trans
    simp only [segment, Fin.addCases_left, ChildBankInit.resize_instruction]
  · intro j
    apply (code ((number a j).natAdd (2 ^ a))).trans
    simp only [segment, Fin.addCases_right, Equiv.symm_apply_apply, resize_instruction]

end PairSimulation.NodeArguments.ChildCode.RegisterBank

end VPVNP
end Computability
end OAI
