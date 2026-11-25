import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentPackedPrivateSum
import OAI.Hierarchy.DescentPrivateExponentRAM
import OAI.Hierarchy.DescentTerminalRowPlan
import OAI.Hierarchy.DescentTerminalSiteOffsets
import OAI.Hierarchy.DescentTerminalPacketSlotFrame
import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentTerminalPositionIssue

namespace OAI
/-! # Banks and memory states of the terminal meter suffix -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalVertexFields
noncomputable section

structure Layout where
  count : DescentPackedPrivateSum.Layout
  exponent : DescentPrivateExponentRAM.Banks
  homes : Bank
  order : ProtocolRAMEndpointSort.Layout
  row : DescentTerminalRowPlan.Layout
  offset : DescentTerminalSiteOffsets.Layout
  directory : DescentTerminalSiteShelves.Directory
  emit : DescentTerminalEmitter.Layout

def Shape.packets (s : Shape) := s.terminal.plane.exteriors*2^(s.terminal.plane.headBits+s.terminal.plane.restBits)

namespace Suffix

variable {w blocks : ℕ} (S : Shape) (L : Layout) (F : MaskedShelf blocks)

def positioned (m : Memory w) :=
  DescentTerminalSiteOffsets.result L.offset S.sites (DescentTerminalRowPlan.result L.row S.sites S.terminal.rows m)

def sockets (m : Memory w) := DescentTerminalPacketSlotRAM.after L.order S.packets S.sites
  (DescentTerminalExteriorPackets.sorted L.homes L.order S.sites S.packets S.sites_pos (positioned S L m))

def pages (m : Memory w) := maskedMem F L.directory S.sites (sockets S L m)
def events (m : Memory w) := DescentTerminalEmitter.issued S.terminal L.emit L.directory (pages S L F m)
def output (m : Memory w) := DescentTerminalEmitter.result S.terminal L.emit (events S L F m)

end Suffix

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
