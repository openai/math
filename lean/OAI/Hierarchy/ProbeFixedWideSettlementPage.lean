import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProtocolRAMCatalystStripLedgerReads
import OAI.Hierarchy.ProtocolRAMCatalystChargedDates
import OAI.Hierarchy.ProtocolRAMCatalystStripOwnerCost
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # Original terminal page number and the order of its physical route accounts -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "cnt" => rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A))
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h

def wideSignedPage (stock : Bank) := TerminalLayout.pageBits v.mesh A stock stride (P).catalogue.rows r num cnt

/-- A fixed order on commodities and reserve columns. The separate resource index in
the native counter is the physical inventory slot or the actual column/axis pair. -/
def wideRouteOrder (h d k : ℕ) : Orders h d k :=
  ⟨(PurchaseInventory.slotEquiv h (Stages h d) k).trans
    (finCongr (PurchaseInventory.card_commodity h (Stages h d) k).symm),Fintype.equivFin _⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
