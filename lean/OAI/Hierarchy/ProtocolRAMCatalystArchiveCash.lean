import OAI.Hierarchy.ProbeCatalystCashRead
import OAI.Hierarchy.ProtocolRAMCatalystArchiveChronology

namespace OAI
/-! # Signed amounts at the literal rows of a priced commit -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Calendar.StockCommit AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical
variable {balls D k count payload w q K : ℕ}

theorem readEntry_bits {R C H E G : Type*} [Fintype C] [Fintype H] [Fintype E]
    {stock : StockCommit} {batch : Batch q D} {m : Memory w}
    (plan : StockCommit.PortPlan stock batch m balls) (ballsAt : R ↪ Fin balls)
    (bound : Fintype.card (Role C H E k)≤D) (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count)
    (idle : Fin count) (positive : 0<K) (width : R→ℕ) (copies : ∀r,batch.copies≤copied K (width r) payload)
    (packet : ∀r,ballsAt r∈liveRows batch m balls→∀c axis,cashWord plan (ballsAt r,catalystPort bound (c,axis))≤batch.copies*width r)
    (support : ∀c,0<cashWord plan c→∃z,portCell ballsAt bound z=c) (cell : Fin balls × Fin D) :
    (readEntry plan ballsAt bound columns keys idle positive width copies packet).bits (finProdFinEquiv cell)=cashWord plan cell :=
  repair_bits ballsAt bound columns keys idle (cashWord plan) _ support cell

/-- A row is indexed by the installed port header. Its native second cash word is precisely
the amount from the funded entry for that row, including ordinary and zero-width slots. -/
theorem priced_amount {R C H E G : Type*} [Fintype C] [Fintype H] [Fintype E]
    (chart : Chart w q D) (date : Attempt) (m : Memory w) (a : StockCommit.Area)
    (s : StockCommit.Sources) (g : StockCommit.LabelSource) (batch : Batch q D)
    (physical : chart.commit date=StockCommit.pricedSegment a s g w batch)
    (active : ready chart (.attempt date) m) (board : StockCommit.EventBoard (StockCommit.fresh a s) w)
    (plan : StockCommit.PortPlan (StockCommit.fresh a s) batch (StockCommit.stageInput a s g
      (PurchaseStage.postOutput (chart.layout date) (repair chart date) (prepared chart date m))) balls)
    (rowOrder : ∀c : Fin balls×Fin D,(plan.enum ⟨c.1,c.2⟩).val=(finProdFinEquiv c).val)
    (ballsAt : R ↪ Fin balls) (bound : Fintype.card (Role C H E k)≤D)
    (columns : R × C ↪ G) (keys : G × Fin k ↪ Fin count) (idle : Fin count)
    (positive : 0<K) (width : R→ℕ) (copies : ∀r,batch.copies≤copied K (width r) payload)
    (packet : ∀r,ballsAt r∈liveRows batch _ balls→∀c axis,cashWord plan (ballsAt r,catalystPort bound (c,axis))≤batch.copies*width r)
    (support : ∀c,0<cashWord plan c→∃z,portCell ballsAt bound z=c)
    (i : Fin (balls*D)) :
    after chart (.attempt date) m (a.direct+a.occurrences+i.val)=
      ((readEntry plan ballsAt bound columns keys idle positive width copies packet).bits i:Word w) := by
  let j := finProdFinEquiv.symm i
  have offset : (plan.enum ⟨j.1,j.2⟩).val=i.val :=
    (rowOrder j).trans (congrArg Fin.val (finProdFinEquiv.apply_symm_apply i))
  have read := priced_debit chart date m a s g batch physical active board (plan.enum ⟨j.1,j.2⟩)
  dsimp only at read
  rw [offset] at read
  have eq := readEntry_bits plan ballsAt bound columns keys idle positive width copies packet support j
  rw [show finProdFinEquiv j=i from finProdFinEquiv.apply_symm_apply _] at eq
  exact read.trans (congrArg (fun n:ℕ=>(n:Word w)) eq.symm)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
