import OAI.Hierarchy.ProtocolRAMCalendarStripBuild
import OAI.Hierarchy.ProtocolRAMNativeLiveFormats

namespace OAI
/-! # The actual payload and purchased programs at the preceding stock address -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open PurchaseStage StripDirectory PortPadding
open scoped Classical Fin.CommRing
variable {z d k q depth r edges w : ℕ}

local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def formats (c : Mesh) (arena : Arena) (initial : ℕ) (s : Boards z d k q depth) :=
  liveFormats c arena initial (build F s)

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
