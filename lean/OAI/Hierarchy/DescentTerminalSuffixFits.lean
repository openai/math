import OAI.Hierarchy.DescentTerminalSuffixData
import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentTerminalStableSortRAM

namespace OAI
/-! # Memory bounds for the physical terminal suffix -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentTerminalVertexFields
noncomputable section
variable (S : Shape) (L : Layout)

def slotBase := DescentTerminalPacketSlotRAM.out L.order S.packets S.sites

namespace Suffix
variable {blocks : ℕ} (F : MaskedShelf blocks)
local notation "rows_" => S.terminal.rows

structure Fits (w : ℕ) : Prop where
  allocator : DescentTerminalRowPlan.Room L.row S.sites rows_ w
  offsets : DescentTerminalSiteOffsets.Room L.offset w S.sites
  sort : DescentTerminalExteriorPackets.SortRoom L.homes L.order w S.packets S.sites
  endSlots : slotBase S L+S.packets<2^w
  pageROM : (guardedMask F S.sites).Fits w L.directory.texture.base
  endPages : L.directory.texture.base+(S.sites+1)<2^w
  leafROM : (DescentTerminalSiteShelves.gather L.directory).Fits w L.emit.leaf.event.base
  endLeaves : L.emit.leaf.event.base+S.terminal.pool<2^w
  issuer : DescentTerminalEmitter.Room S.terminal L.emit w

end Suffix
end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
