import OAI.Hierarchy.DescentTerminalSliceRaw
import OAI.Hierarchy.DescentTerminalSliceScale
import OAI.Hierarchy.DescentTerminalPointerPrice
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! # Native width of the recovered terminal operand arrays -/
namespace Hierarchy.DescentTerminalSliceShelf
open DescentCompiler.TerminalScale DescentDatedAddressBook DescentTerminalPointerDigits Filter
noncomputable section

theorem reset_field (v:ResetOutput) :
    v.primitive.chart.bits*v.primitive.chart.nodes≤v.groupWidth ∧ v.nodeBits*v.nodes≤v.groupWidth := by
  constructor
  · exact (Nat.le_add_right ..).trans (v.groupWidth_fit (Or.inr (show
      v.primitive.chart.bits*v.primitive.chart.nodes+v.primitive.chart.bits∈v.receiverUnits by simp [ResetOutput.receiverUnits])))
  · exact (Nat.le_add_right ..).trans (v.groupWidth_fit (Or.inr (show
      v.nodeBits*v.nodes+v.nodeBits∈v.receiverUnits by simp [ResetOutput.receiverUnits])))

theorem width_of_reset (v:ResetOutput) (groups:ℕ) (nodes:v.primitive.chart.nodes=v.nodes) :
    physicalWidth groups v.nodes v.primitive.chart.bits v.nodeBits≤groups*v.groupWidth := by
  have bound:=reset_field v
  rw [nodes] at bound
  unfold physicalWidth
  apply Nat.mul_le_mul_left
  rw [←Nat.mul_max_mul_left]
  exact max_le (by simpa only [Nat.mul_comm v.nodes] using bound.1)
    (by simpa only [Nat.mul_comm v.nodes] using bound.2)

theorem table_size (d L h:ℕ) (positive:0<L) (room:d*L+Nat.clog 2 (L+1)≤h/2) :
    DescentTerminalPointerFrame.size L d≤2*2^(h/2) :=
  table_words d L h positive room


end
end Hierarchy.DescentTerminalSliceShelf

end OAI
