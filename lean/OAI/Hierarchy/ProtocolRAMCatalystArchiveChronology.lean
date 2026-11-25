import OAI.Hierarchy.ProtocolRAMCatalystDatedReads
import OAI.Hierarchy.ProtocolRAMStockCommitDebit

namespace OAI
/-! # Reading a dated debit from the physical commitment -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w q d : ℕ}

/-- The second direct column of the priced commit is the signed cash debit.
This reads the very occurrence that the installed batch committed. -/
theorem priced_debit (C : Chart w q d) (e : Attempt) (m : Memory w)
    (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource)
    (b : Batch q d) (physical : C.commit e=StockCommit.pricedSegment a s g w b)
    (mounted : ready C (.attempt e) m) (board : StockCommit.EventBoard (StockCommit.fresh a s) w)
    (j : Fin a.occurrences) :
    let st := StockCommit.fresh a s
    let v := PurchaseStage.postOutput (C.layout e) (repair C e) (prepared C e m)
    let u := StockCommit.stageInput a s g v
    after C (.attempt e) m (a.direct+a.occurrences+j.val)=
      ((if RepairHistogram.kind (goods:=a.goods) st.plan.bank st.columns u j=none
        then RepairHistogram.consumedBits st.columns u j else 0 : ℕ):Word w) := by
  intro st v u
  obtain ⟨_,_,_,_,_,_,_,_,_,_,commitReady,_,_⟩ := mounted
  rw [physical] at commitReady
  rw [Calendar.after,physical,StockCommit.priced_after]
  have ok : (st.native w a.rows b).ready u := commitReady.2.2
  have out := (st.read_direct b u j ok board.chargeFits board.order
    (board.hit b u ok j) board.bound (board.keep j)).2
  exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun val : ℕ=>(val:Word w)) out)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
