import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentTerminalPacketSlotRAM
import OAI.Hierarchy.DescentTerminalSiteOffsets

namespace OAI
/-! # Exact native hardware counts for site offsets and packet ordinals -/
namespace Hierarchy
open DescentStaticWordColumn

/-- Counting and scattering use fixed loop bodies for every input length. -/
theorem ProtocolRAMEndpointSort.program_names (L : ProtocolRAMEndpointSort.Layout) (w n sites : ℕ) :
    names (ProtocolRAMEndpointSort.program L w n sites) = 101 := by
  simp only [ProtocolRAMEndpointSort.program, ProtocolRAMSiteCounts.program,
    ProtocolRAMEndpointPrefix.exclusive, names_seq]
  rfl

/-- The first lookup fetches a site start and the second fetches its offset. -/
theorem DescentTerminalSiteOffsets.program_names (L : DescentTerminalSiteOffsets.Layout) (w sites : ℕ) :
    names (DescentTerminalSiteOffsets.program L w sites) = 59 := by
  rw [DescentTerminalSiteOffsets.program, names_scan]
  rfl

/-- The guarded home scan, stable sort and site-relative rank scan occupy 343 names. -/
theorem DescentTerminalPacketSlotRAM.program_names (b : ProtocolRAM.Bank)
    (L : ProtocolRAMEndpointSort.Layout) (w n sites : ℕ) :
    names (DescentTerminalPacketSlotRAM.program b L w n sites) = 343 := by
  simp only [DescentTerminalPacketSlotRAM.program, DescentTerminalExteriorPackets.sortedProgram,
    names_seq, names_scan, ProtocolRAMEndpointSort.program_names]
  rfl

end Hierarchy

end OAI
