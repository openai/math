import OAI.Hierarchy.ProbePaidStripTree
import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter
import OAI.Hierarchy.ProtocolRAMCommittedTape

namespace OAI
/-! # A nonzero permanent broadcast cell comes from an actual committed ball -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM StockCommit RepairHistogram
open scoped Fin.CommRing Classical

variable {W q d : ℕ}

theorem archived_broadcast (C : Chart W q d) (flag : ℕ) (m : Memory W) (pre post : List Event)
    (event : Attempt) (split : events C.mesh=pre++(.attempt event)::post)
    (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource) (b : Batch q d)
    (j : Fin a.rows) (v : Memory W) (physical : C.commit event=StockCommit.pricedSegment a s g W b)
    (snap : PurchaseStage.postOutput (C.layout event) (repair C event) (prepared C event (run C pre m))=v)
    (ready : (StockCommit.pricedSegment a s g W b).ready v)
    (bc : BroadcastRoom (StockCommit.fresh a s) b a.rows W)
    (qFit : q≤2^W) (copyFit : b.copies<2^W) (sumFit : q*b.copies<2^W)
    (eligible : mounted C post (after C (.attempt event) (run C pre m)))
    (keep : ∀x∈post,protected C (a.broadcast+j.val) x) (apart : a.broadcast+j.val≠flag) :
    let st:=StockCommit.fresh a s
    let u:=StockCommit.stageInput a s g v
    checkedOut C flag m (a.broadcast+j.val)=if committed b u (j.val:Word W)
      then st.price.read u (b.packet.eval u (j.val:Word W)) else 0 := by
  rw [archived_word C flag _ m pre post _ split eligible keep apart,after,physical,snap,StockCommit.priced_after]
  exact (StockCommit.fresh a s).read_broadcast b _ j ready.2.2 bc.fits qFit copyFit sumFit (bc.keeps j)

theorem broadcast_live {Ball : Type*} (a : Area) (s : Sources) (g : LabelSource)
    (b : Batch q d) (m v : Memory W) (whereAt : Ball ↪ Fin a.rows)
    (archive : ∀j : Fin a.rows,m (a.broadcast+j.val)=
      if committed b (stageInput a s g v) (j.val:Word W)
      then (fresh a s).price.read (stageInput a s g v) (b.packet.eval (stageInput a s g v) (j.val:Word W)) else 0)
    (owners : ∀j∈liveRows b (stageInput a s g v) a.rows,∃u,whereAt u=j)
    (j : Fin a.rows) (positive : 0<(m (a.broadcast+j.val)).val) : ∃u,whereAt u=j := by
  apply owners
  by_contra unused
  have no : ¬committed b (stageInput a s g v) (j.val:Word W) := by simpa [liveRows] using unused
  rw [archive j,ite_eq_right no] at positive
  exact Nat.lt_irrefl _ positive

end Hierarchy.ProtocolRAM.Calendar

end
end OAI
