import OAI.Hierarchy.DescentTerminalRowPlan
import OAI.Hierarchy.DescentStaticWordColumn

namespace OAI
/-! # Fixed native syntax of the entire row allocator -/

namespace Hierarchy.DescentTerminalRowPlan
open ProtocolRAM DescentStaticWordColumn DescentTerminalSpanBook DescentTerminalLocalPortBook
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr

set_option maxRecDepth 4096 in
/-- All phase counts here refer to the linked output, including the two
scatter public words, the five temporary registers and its nine labels. -/
theorem program_names (L : Layout) (w S n : ℕ) : names (program (w:=w) L S n)=1257 := by
  have packed : names (DescentTerminalBinPackCheap.program w L.counts.base L.boundaries L.cursors.base S)=207 := by
    simp only [names,DescentTerminalBinPackCheap.program,PhysicalInputPhases.writing,
      Term.labels_eq,DescentTerminalBinPackCheap.cost]
  have prefixSize : names (DescentTerminalHeaderPrefixRAM.program w L.locate.number.base n
      .add (.lookup L.locate.marker .row))=67 := by
    simp only [names,DescentTerminalHeaderPrefixRAM.program,PhysicalInputPhases.writing,
      Term.labels_eq,DescentTerminalHeaderPrefixRAM.binds]; rfl
  have scatter : names (EffectSeed.scatter w L.markedScratch S)=16 := rfl
  simp only [program,DescentTerminalBinPackCheap.headerProgram,MarkerBanks.program,
    DescentTerminalHeaderScatter.program,Cursors.program,names_seq,names_scan,packed,prefixSize,scatter]
  rfl

end Hierarchy.DescentTerminalRowPlan

end OAI
