import OAI.Hierarchy.DescentTerminalCompiledPrefix
import OAI.Hierarchy.DescentTerminalRowPlanNames
import OAI.Hierarchy.DescentTerminalRowArenaSortNames

namespace OAI
/-! # All native labels, registers and public slots before the terminal mask -/

namespace Hierarchy.DescentTerminalCompiledPrefix.Suffix
open DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure

theorem slots_names (S : Shape) (L : Layout) (w : ℕ) :
    names (((DescentTerminalRowPlan.program (w:=w) L.row S.sites S.terminal.rows).seq
      (DescentTerminalSiteOffsets.program L.offset w S.sites)).seq
      (DescentTerminalPacketSlotRAM.program L.homes L.order w S.packets S.sites))=1659 := by
  rw [names_seq,names_seq,DescentTerminalRowPlan.program_names,DescentTerminalSiteOffsets.program_names,
    DescentTerminalPacketSlotRAM.program_names]

end Hierarchy.DescentTerminalCompiledPrefix.Suffix

end OAI
