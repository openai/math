import OAI.Hierarchy.DescentPriorOperandColumns
import OAI.Hierarchy.DescentColumnHardware

namespace OAI
/-! # Hardware tariff for the prior-operand scalar extractor -/
namespace Hierarchy.DescentPriorOperandColumns
open DescentOrdinaryAtomFieldRAM ProtocolRAM
noncomputable section

theorem names {P : ℕ} (old : Fin P→Bank) (a K M rows w base out : ℕ) :
    DescentStaticWordColumn.names (program old a K M rows w base out) ≤
      15*(K*2^((a*K)*M)+1)+(15+(P*K)*(11+4*12)) := by
  have bound : ∀e∈expressions old a K M base,e.work≤12:=by
    intro e h;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp h;exact le_rfl
  have price:=ScalarOperand.labels_registers (expressions old a K M base) out rows 12 w bound
  unfold program
  rw [DescentStaticWordColumn.names_seq,ROM.mount,DescentStaticWordColumn.names_mount]
  apply Nat.add_le_add_left
  simpa only [DescentStaticWordColumn.names,expressions,List.length_ofFn] using price

end
end Hierarchy.DescentPriorOperandColumns

end OAI
