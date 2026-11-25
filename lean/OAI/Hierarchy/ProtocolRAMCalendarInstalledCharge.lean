import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCalendarPhysicalCharges

namespace OAI
/-! # Reading an attempt's actual prepaid installed-width charges from terminal RAM -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native RepairHistogram
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {z d k q goods r edges W : ℕ}

/-- The positive component of the genuine event bill is exactly the physical
length times the three separately installed sets of widths at a paid attempt.
Direct rows are only queried when they contribute positive width. -/
theorem Format.installed_charge_of_direct (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (forest routes : Traversals) (bound payload : ℕ)
    (m : Memory W) (len : Fin edges→ℝ) (cost mate : Fin p.occurrences→ℝ)
    (tree : Fin p.pricedArea.rows→List (Fin edges)) (core : Fin p.pricedArea.goods→List (Fin edges))
    (flags count : ℕ) (opening : Fin count→ℝ)
    (direct : (PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)).toll m len payload=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*cost i)/payload)
    (second : ((p.mateSlices forest).map (fun t=>t.toll m len payload)).sum=
      (∑i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*mate i)/payload)
    (forestAt : forest.Reads m tree) (routesAt : routes.Reads m core)
    (maxFit : bound<2^W) (copiesFit : p.board.batch.copies<2^W)
    (bits : ∀i : Fin p.pricedArea.rows,(m (p.pricedArea.broadcast+i.val)).val≤bound)
    (full : ∀i : Fin p.pricedArea.rows,p.board.batch.copies*(m (p.pricedArea.broadcast+i.val)).val<2^W) :
    ((p.paidSlices sink idBase role ids forest routes bound).map (fun t=>t.toll m len payload)).sum=
      (charges ((StockCommit.fresh p.pricedArea p.stockSource).eventColumns flags)
        p.occurrences p.pricedArea.rows p.pricedArea.goods count m payload p.board.batch.copies (fun i=>cost i+mate i)
        (fun i=>((tree i).map len).sum) (fun i=>((core i).map len).sum) opening).install := by
  simp only [Format.paidSlices,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,second]
  rw [direct,
    forest.broadcast_toll p.pricedArea m payload p.board.batch.copies bound len tree forestAt maxFit copiesFit bits full,
    routes.spill_toll p.pricedArea m payload len core routesAt]
  change _=
    (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*(cost i+mate i))/payload+
    (∑ i : Fin p.pricedArea.rows,(p.board.batch.copies:ℝ)*(((tree i).map len).sum*(m (p.pricedArea.broadcast+i.val)).val))/payload+
    ∑ i : Fin p.pricedArea.goods,((m (p.pricedArea.output+p.pricedArea.goods+p.pricedArea.goods+i.val)).val:ℝ)/payload*
      ((core i).map len).sum
  have broadcast (i : Fin p.pricedArea.rows) :
      ((tree i).map len).sum*((p.board.batch.copies*(m (p.pricedArea.broadcast+i.val)).val:ℕ):ℝ)/payload=
        (p.board.batch.copies:ℝ)*(((tree i).map len).sum*(m (p.pricedArea.broadcast+i.val)).val)/payload := by
    push_cast;ring
  have spill (i : Fin p.pricedArea.goods) :
      ((core i).map len).sum*((m (p.pricedArea.output+p.pricedArea.goods+p.pricedArea.goods+i.val)).val/payload:ℝ)=
        ((m (p.pricedArea.output+p.pricedArea.goods+p.pricedArea.goods+i.val)).val:ℝ)/payload*((core i).map len).sum :=
    mul_comm ..
  simp only [mul_add,Finset.sum_add_distrib,add_div,Finset.sum_div,broadcast,spill]
  ring

theorem Format.installed_charge (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (forest routes : Traversals) (bound payload : ℕ)
    (m : Memory W) (len : Fin edges→ℝ) (cost mate : Fin p.occurrences→ℝ)
    (tree : Fin p.pricedArea.rows→List (Fin edges)) (core : Fin p.pricedArea.goods→List (Fin edges))
    (flags count : ℕ) (opening : Fin count→ℝ)
    (width : p.occurrences≤2^W)
    (hit : ∀i : Fin p.occurrences,(m (p.pricedArea.direct+i.val)).val≠0→∃ e : Fin edges,
      ((p.labelSource sink idBase role ids).edge.eval m (i.val:Word W)).val=e.val ∧ len e=cost i)
    (second : ((p.mateSlices forest).map (fun t=>t.toll m len payload)).sum=
      (∑i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*mate i)/payload)
    (forestAt : forest.Reads m tree) (routesAt : routes.Reads m core)
    (maxFit : bound<2^W) (copiesFit : p.board.batch.copies<2^W)
    (bits : ∀i : Fin p.pricedArea.rows,(m (p.pricedArea.broadcast+i.val)).val≤bound)
    (full : ∀i : Fin p.pricedArea.rows,p.board.batch.copies*(m (p.pricedArea.broadcast+i.val)).val<2^W) :
    ((p.paidSlices sink idBase role ids forest routes bound).map (fun t=>t.toll m len payload)).sum=
      (charges ((StockCommit.fresh p.pricedArea p.stockSource).eventColumns flags)
        p.occurrences p.pricedArea.rows p.pricedArea.goods count m payload p.board.batch.copies (fun i=>cost i+mate i)
        (fun i=>((tree i).map len).sum) (fun i=>((core i).map len).sum) opening).install :=
  p.installed_charge_of_direct sink idBase role ids forest routes bound payload m len cost mate tree core
    flags count opening (p.visible_direct_toll sink idBase role ids m len payload cost width hit) second
    forestAt routesAt maxFit copiesFit bits full

theorem Format.two_radii_charge (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (forest routes : Traversals) (bound payload : ℕ)
    (m : Memory W) (len : Fin edges→ℝ) (cost : Fin p.occurrences→ℝ) (mask second : Expr) (M : ℝ)
    (tree : Fin p.pricedArea.rows→List (Fin edges)) (core : Fin p.pricedArea.goods→List (Fin edges))
    (flags count : ℕ) (opening : Fin count→ℝ)
    (width : p.occurrences≤2^W)
    (hit : ∀i : Fin p.occurrences,(m (p.pricedArea.direct+i.val)).val≠0→∃ e : Fin edges,
      ((p.labelSource sink idBase role ids).edge.eval m (i.val:Word W)).val=e.val ∧ len e=cost i)
    (kind : forest.catalystMate=some (mask,second))
    (reach : ∀i : Fin p.occurrences,mask.eval m (i.val:Word W)≠0→(m (p.pricedArea.direct+i.val)).val≠0→
      ∃e : Fin edges,(second.eval m (i.val:Word W)).val=e.val ∧ len e=M)
    (forestAt : forest.Reads m tree) (routesAt : routes.Reads m core)
    (maxFit : bound<2^W) (copiesFit : p.board.batch.copies<2^W)
    (bits : ∀i : Fin p.pricedArea.rows,(m (p.pricedArea.broadcast+i.val)).val≤bound)
    (full : ∀i : Fin p.pricedArea.rows,p.board.batch.copies*(m (p.pricedArea.broadcast+i.val)).val<2^W) :
    ((p.paidSlices sink idBase role ids forest routes bound).map (fun t=>t.toll m len payload)).sum=
      (charges ((StockCommit.fresh p.pricedArea p.stockSource).eventColumns flags)
        p.occurrences p.pricedArea.rows p.pricedArea.goods count m payload p.board.batch.copies (fun i=>cost i+(if mask.eval m (i.val:Word W)=0 then 0 else M))
        (fun i=>((tree i).map len).sum) (fun i=>((core i).map len).sum) opening).install := by
  apply p.installed_charge sink idBase role ids forest routes bound payload m len cost
    (fun i=>if mask.eval m (i.val:Word W)=0 then 0 else M) tree core flags count opening width hit
    (p.mate_toll forest mask second m len M payload width kind reach) forestAt routesAt maxFit copiesFit bits full

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
