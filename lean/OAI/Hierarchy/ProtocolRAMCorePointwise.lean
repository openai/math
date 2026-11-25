import OAI.Hierarchy.ProtocolRAMAdviceLocal
import OAI.Hierarchy.ProtocolRAMCoreRouteImage

namespace OAI
/-! # Coordinate independence of the fixed route, column and public core loaders -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open private put from OAI.Hierarchy.ProtocolRAMColumnDirectory

private theorem load_local {w : ℕ} (base h d k : ℕ) : AdviceLocal (load (w:=w) base h d k) := by
  intro m n x same
  simp only [load,put,fillSegment,same]
end Hierarchy.ProtocolRAM.BoughtSockets.ColumnROM

namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k attempts R K H : ℕ} {S : PurchaseSampler}

/-- The complete core prefix installer reads its input only to preserve the
word at the requested address outside all installed ROM segments. -/
theorem low_local (order : Fin R≃Edges S z (2^W) k) (M : ℕ)
    (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory
      (TaggedShorterSupergroups.reserved z W (copies k attempts)) H) (depth : ℕ) :
    AdviceLocal (low order M groups packed depth) := by
  intro m n x h
  let base := CoreCatalogue.top z W K packed.groups H R
  let dir := directoryBase S z W k attempts depth K packed.groups H R
  have directory : CoreLookup.mount dir order m x = CoreLookup.mount dir order n x := by
    simp only [CoreLookup.mount,fillSegment,h]
  have columns := ColumnROM.load_local (w:=Native.wordBits z (2^W) Native.copies) base z (2^W) k
  have atColumn := columns _ _ x directory
  dsimp only [base,dir] at atColumn
  simp only [low,CoreCatalogue.initial,CoreCatalogue.mountHeader,SiteROM.image,
    ProtocolRAMSupergroupDirectory.mount,ProtocolRAMSupergroupDirectory.store,SiteROM.mount,
    ReportGroupROM.load,Public.load,StockCommit.PortHeader.load,RepairHistogram.pairAdvice,
    fillSegment,atColumn]

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
