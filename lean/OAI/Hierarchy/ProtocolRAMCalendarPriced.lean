import OAI.Hierarchy.ProtocolRAMNativePricedChart
import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMCalendarInstalled
import OAI.Hierarchy.ProtocolRAMReportedChargeKeys

namespace OAI
/-! # Installing the reported metric on each chronological repair occurrence -/

namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage ProbeStage.Native PurchaseStage
open ThreeFlat.RAM
noncomputable section
variable {z d k q goods r edges w : ℕ}

theorem Format.priced_clock (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (b : Batch q goods) :
    (p.pricedCommit sink idBase role ids b).ticks =
      ((p.labelSource sink idBase role ids).pass p.occurrences).clock+
      (StockCommit.freshSegment p.pricedArea p.stockSource (wordBits z d copies) b).ticks := rfl

theorem Format.priced_text (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (b : Batch q goods) :
    text (p.pricedCommit sink idBase role ids b).native=
      rowText ((p.labelSource sink idBase role ids).pass p.occurrences).term+
      text (StockCommit.freshSegment p.pricedArea p.stockSource (wordBits z d copies) b).native := by
  rw [Format.pricedCommit,StockCommit.pricedSegment,text_seq]
  exact congrArg (·+_) (text_scan ..)

theorem Format.label_frame (p : Format z d k q goods) (_sink : Sink r edges) (_idBase : ℕ)
    (_role : Expr) (_ids : Fin goods→Expr) (i : Fin p.occurrences) (b : Batch q goods) :
    (StockCommit.freshSegment p.pricedArea p.stockSource (wordBits z d copies) b).keeps (p.labelStart+i.val) := by
  apply StockCommit.fresh_keeps
  left
  change p.labelStart+i.val<p.labelStart+p.occurrences
  omega

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
