import OAI.Hierarchy.ProtocolRAMNativeOccurrenceFormat
import OAI.Hierarchy.ProtocolRAMStockCommitPortSources
import OAI.Hierarchy.ProtocolRAMOccurrenceHeader
import OAI.Hierarchy.ProtocolRAMCommittedTape
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout

namespace OAI
/-! # Physical occurrence-to-ball and port projection for the committed repair tape -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w q d : ℕ}

theorem fresh_broadcastRoom (a : Area) (s : Sources) (b : Batch q d) (h : PrefixFits a s b)
    (room : a.stop<2^w) : BroadcastRoom (fresh a s) b a.rows w := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  refine ⟨(RepairHistogram.broadcastTerm b s.price).fits_of_inputEnd (out:=a.direct) (h.broadcast.trans (by change a.start≤a.direct;omega)) (by omega),?_⟩
  intro j
  have small := j.isLt
  change RepairHistogram.commit_keeps (a.plan s) a.occurrences a.goods (a.broadcast+j.val)
  simp only [RepairHistogram.commit_keeps,Area.plan,Area.bank]
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem fresh_stockRoom (a : Area) (s : Sources) (b : Batch q d) (h : PrefixFits a s b)
    (payload cap : ℕ) (wide : 4≤2^w) (room : a.stop<2^w) (limit : a.limit=cap*payload) (price : a.limit<2^w) :
    StockRoom (fresh a s) w payload cap := by
  obtain ⟨goods,seed,fees,flags,tape,capEnd,capOut,last⟩ := a.order
  have slot : (RepairHistogram.destination a.start a.goods s.slot).inputEnd≤a.start :=
    by simp [RepairHistogram.destination,Expr.inputEnd,h.slot]
  have mono : a.start≤a.direct := by omega
  have fit : a.direct<2^w := by omega
  exact ⟨(RepairHistogram.destination a.start a.goods s.slot).fits_of_inputEnd (slot.trans mono) fit,
    s.credit.fits_of_inputEnd (h.credit.trans mono) fit,s.charge.fits_of_inputEnd (h.charge.trans mono) fit,
    by change a.start+a.goods≤a.direct;omega,by change a.start+a.goods≤a.src;omega,wide,limit,price,rfl,goods.le,goods.le,goods.le⟩


end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
