import OAI.Hierarchy.DescentPreviousOperandLimit
import OAI.Hierarchy.DescentResetRegisterBank

namespace OAI
/-! # The full rounded extent of the reset operand register -/

namespace Hierarchy.DescentResetNodeBooks

open DescentDatedPriorOperand DescentOperandStateBanks ProtocolRAM

/-- The reset writer and the previous operand directory have the same exclusive
end address, including the reserved dyadic padding. -/
theorem previous_limit (L : Layout) (floor bits : ℕ) :
    L.previousLimit (output floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes) =
      endAddress floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes := by
  simp only [Layout.previousLimit, Layout.rows, endAddress, rounded, rows, Nat.mul_assoc]

/-- The scalar phase precedes the start and the full rounded end of the prior
operand register. This includes an empty set of pages or blocks. -/
theorem output_window (L : Layout) (floor bits : ℕ) :
    let first := output floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes
    floor ≤ first ∧ first ≤ L.previousLimit first := by
  exact ⟨Nat.le_add_right _ _, (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)⟩

/-- Every numbered reset bank, including the final padded bank, fits in the
machine word and in the published complete register. -/
theorem register_room (L : Layout) (floor bits w : ℕ) (pg : Pages L.operands) (x : Fin L.blocks)
    (space : endAddress floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes < 2^w) :
    (bank floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes
      (finProdFinEquiv (pg, x))).Fits w
      (endAddress floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes) ∧
    L.rows ≤ (bank floor ((7 * L.operands) * L.blocks) L.nodes L.hosts L.groups bits L.lanes
      (finProdFinEquiv (pg, x))).size := by
  have fit := L.previous_fit _ _ w (previous_limit L floor bits).le space x pg
  rw [previous_bank] at fit
  exact ⟨fit, capacity _⟩

end Hierarchy.DescentResetNodeBooks

end OAI
