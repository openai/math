import OAI.Hierarchy.ProtocolRAMNativeOccurrenceFormat
import OAI.Hierarchy.ProtocolRAMCalendarPriced
import OAI.Hierarchy.ProtocolRAMCommittedPortLayout

namespace OAI
/-! # Bind the mutable occurrence gate after the real repair-mask addresses have been placed -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage ProbeStage.Native PurchaseStage RepairHistogram StockCommit
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k q goods w r edges : ℕ}

/-- Prefixing the price labels and copying the old global stock preserve the
original physical occurrence directory at its public position. -/
theorem Format.occurrenceLoaded (p : Format z d k q goods) (start : ℕ)
    (g : LabelSource) (out : Memory w)
    (loaded : (p.occurrenceHeader start).Loaded out)
    (header : (p.occurrenceHeader start).stop≤g.out) (labels : g.out≤p.pricedArea.start) :
    let s := (p.withOccurrenceHeader start).stockSource
    (p.occurrenceHeader start).Loaded ((p.pricedArea.seed s).apply ((g.pass p.occurrences).apply out)) := by
  apply (p.occurrenceHeader start).seed_loaded _ _ _ _ (header.trans labels)
  exact loaded.frame (fun x _ hx => ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (hx.trans_le header)))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
