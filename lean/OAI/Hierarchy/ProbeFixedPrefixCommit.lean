import OAI.Hierarchy.ProtocolRAMOccurrenceBounds
import OAI.Hierarchy.ProbeFixedPrefixBatch
import OAI.Hierarchy.ProtocolRAMCalendarOccurrenceFormat

namespace OAI
/-! # Commit expression bounds for the installed physical occurrence directory -/
namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage StockCommit
noncomputable section
variable {z d k q goods cut : ℕ}

theorem Format.occurrence_prefix (f : Format z d k q goods) (start : ℕ)
    (sealed : f.withOccurrenceHeader start=f)
    (batch : (enabledBatch f.market.layout f.board).Before f.pricedArea.start)
    (slot : f.stockSource.slot.inputEnd≤f.pricedArea.start)
    (wire : ∀i j,(f.board.wire i j).inputEnd≤f.pricedArea.start)
    (old : f.stockSource.old.base+f.stockSource.old.size≤f.pricedArea.start)
    (reserve : f.stockSource.reserve.base+f.stockSource.reserve.size≤f.pricedArea.start)
    (half : f.stockSource.half.base+f.stockSource.half.size≤f.pricedArea.start)
    (mode : f.stockSource.mode.inputEnd≤f.pricedArea.start)
    (price : f.stockSource.price.base+f.stockSource.price.size≤f.pricedArea.start)
    (header : (f.occurrenceHeader start).stop≤f.pricedArea.start) :
    PrefixFits f.pricedArea f.stockSource (enabledBatch f.market.layout f.board) := by
  let h:=f.occurrenceHeader start
  obtain ⟨ball,port,own,parity⟩:=h.input_ends header
  have side:=batch.fromBatch h.owner h.parity (.lit 0) h.ballTerm h.fieldTerm f.board.wire ball port wire
  have credit : f.stockSource.credit.inputEnd≤f.pricedArea.start := by
    calc
      _ = (f.withOccurrenceHeader start).stockSource.credit.inputEnd := by rw [sealed]
      _ ≤ f.pricedArea.start := side.1
  have charge : f.stockSource.charge.inputEnd≤f.pricedArea.start := by
    calc
      _ = (f.withOccurrenceHeader start).stockSource.charge.inputEnd := by rw [sealed]
      _ ≤ f.pricedArea.start := side.2
  have ownerFit : f.stockSource.owner.base+f.stockSource.owner.size≤f.pricedArea.start := by
    calc
      _ = (f.withOccurrenceHeader start).stockSource.owner.base+(f.withOccurrenceHeader start).stockSource.owner.size := by rw [sealed]
      _ ≤ f.pricedArea.start := own
  have parityFit : f.stockSource.parity.base+f.stockSource.parity.size≤f.pricedArea.start := by
    calc
      _ = (f.withOccurrenceHeader start).stockSource.parity.base+(f.withOccurrenceHeader start).stockSource.parity.size := by rw [sealed]
      _ ≤ f.pricedArea.start := parity
  refine ⟨old,reserve,half,mode,?_,credit,charge,slot,batch.broadcast _ price,ownerFit,parityFit⟩
  let index:=Expr.lookup f.stockSource.owner .row
  have indexFit : index.inputEnd≤f.pricedArea.start := max_le ownerFit (Nat.zero_le _)
  have destFit : (RepairHistogram.destination f.pricedArea.start f.pricedArea.goods f.stockSource.slot).inputEnd≤f.pricedArea.start :=
    max_le (Nat.zero_le _) (max_le (max_le slot (Nat.zero_le _)) (max_le slot (Nat.zero_le _)))
  exact max_le (max_le (max_le parityFit (Nat.zero_le _)) (Nat.zero_le _))
    (max_le (InputEnd.atRow _ index destFit indexFit)
      (max_le (InputEnd.atRow _ index credit indexFit) (InputEnd.atRow _ index charge indexFit)))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
