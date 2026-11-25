import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentResetNodeBooks

namespace OAI
namespace Hierarchy.DescentResetNodeBooks

open DescentDatedPriorOperand DescentOperandStateBanks

/-- The previous operand directory and the reset node books assign the same bank
to each physical page and block. -/
theorem previous_bank (L : Layout) (floor bits : ℕ) (pg : Pages L.operands) (x : Fin L.blocks) :
    previousBank L
      (output floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes) x pg =
      bank floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes
        (finProdFinEquiv (pg, x)) := by
  simp only [previousBank, bank, finProdFinEquiv_apply_val, Layout.rows, rows]
  congr 1; ring


end Hierarchy.DescentResetNodeBooks

end OAI
