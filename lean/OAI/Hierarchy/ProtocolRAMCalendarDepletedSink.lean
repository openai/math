import OAI.Hierarchy.ProtocolRAMCalendarSettlement
import OAI.Hierarchy.ProtocolRAMReserveUse
import OAI.Hierarchy.ProtocolRAMCalendarCommitPrice
import OAI.Hierarchy.ProtocolRAMCalendarSegments

namespace OAI
/-! # Reconciling physical reserve usage before the final routing report -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe
open scoped Fin.CommRing Classical

variable {W q d r edges n count : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

/-- Look back from the actual checked memory to the committed word of a
particular event, through all later native writes and the final verdict. -/
theorem archived_word (C : Chart W q d) (flag x : ℕ) (m : Memory W) (pre post : List Event)
    (ev : Event) (split : events C.mesh=pre++ev::post)
    (eligible : mounted C post (after C ev (run C pre m)))
    (keep : ∀e∈post,protected C x e) (apart : x≠flag) :
    checkedOut C flag m x = after C ev (run C pre m) x := by
  have off : x<flag ∨ flag+1≤x := by omega
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off,split,run_append,run]
  exact run_frame C post _ x eligible keep

/-- The pointer installed at an ordinary catalyst demand reads the consumed
word of that event's sparse physical commit, even after the final guard.
The site-ID word can use the same `archived_word` on its endpoint column. -/
theorem archived_debit (C : Chart W q d) (flag : ℕ) (m : Memory W) (pre post : List Event)
    (a : Attempt) (split : events C.mesh=pre++(.attempt a)::post)
    (s : StockCommit) (b : Batch q d) (rows : ℕ) (j : Fin s.occurrences)
    (v : Memory W) (physical : (C.commit a)=(s.native W rows b))
    (snapshot : PurchaseStage.postOutput (C.layout a) (repair C a) (prepared C a (run C pre m))=v)
    (ready : (s.native W rows b).ready v)
    (inputs : (RepairHistogram.ordinaryTerm s.columns s.plan s.goods s.columns.charge).Fits W s.direct)
    (order : s.direct+s.occurrences+s.occurrences≤ s.broadcast)
    (hit : s.plan.bank.base≤RepairHistogram.address s.columns v j ∧
      RepairHistogram.address s.columns v j≤ s.plan.bank.base+s.goods)
    (bounded : s.plan.bank.base+s.goods<2^W)
    (preserved : RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+j.val) ∧
      RepairHistogram.commit_keeps s.plan s.occurrences s.goods (s.direct+s.occurrences+j.val))
    (eligible : mounted C post (after C (.attempt a) (run C pre m)))
    (keep : ∀e∈post,protected C (s.direct+s.occurrences+j.val) e)
    (apart : s.direct+s.occurrences+j.val≠flag) :
    (checkedOut C flag m (s.direct+s.occurrences+j.val)).val =
      if RepairHistogram.kind (goods:=s.goods) s.plan.bank s.columns v j=none then
        RepairHistogram.consumedBits s.columns v j else 0 := by
  rw [archived_word C flag _ m pre post _ split eligible keep apart,after,physical,snapshot]
  exact (s.read_direct b v j ready inputs order hit bounded preserved).2

def reconcile (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (a : ReserveUse.Archive)
    (count n reserve : ℕ) :=
  ((checked C flag).seq (ReserveUse.native W a f.banks count n reserve)).seq (f.native W)

theorem reconcile_cheap (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (a : ReserveUse.Archive)
    (count n reserve : ℕ) : CheapCode (reconcile C flag f a count n reserve) :=
  @cheap_seq W ((checked C flag).seq (ReserveUse.native W a f.banks count n reserve)) (f.native W)
    (@cheap_seq W (checked C flag) (ReserveUse.native W a f.banks count n reserve)
      (@checked_cheap W q d C flag) (@ReserveUse.cheap W a f.banks count n reserve))
    (@RouteSettlement.reporter_cheap W f.source f.table f.destination edges r f.banks f.owners f.geometry)

omit [Fintype I] [Fintype J] in
theorem reconcile_exec (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (a : ReserveUse.Archive)
    (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory W)
    (ready : mounted C (events C.mesh) m) (fit : (historyFlag C (events C.mesh)).Fits W flag)
    (room : flag+1<2^W) (archive : ReserveUse.Mounted a f.banks reserve site debit (checkedOut C flag m))
    (sink : f.Mounted (ReserveUse.output a f.banks reserve site debit (checkedOut C flag m)) e ci cj) :
    (reconcile C flag f a count n reserve).Exec m
      (f.output (ReserveUse.output a f.banks reserve site debit (checkedOut C flag m)) e ci cj)
      (checkedCost C+ReserveUse.clock a f.banks count n reserve+f.clock) := by
  exact Procedure.Exec.then
    (Procedure.Exec.then (checked_exec C flag m ready fit room)
      (ReserveUse.exec a f.banks reserve site debit (checkedOut C flag m) archive))
    (f.exec _ e ci cj sink)

omit [Fintype I] [Fintype J] in
theorem reconcile_frame (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (a : ReserveUse.Archive)
    (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory W) (x : ℕ)
    (res : x<f.banks.reserved.base) (used : x<f.banks.used.base) (scratch : x<a.scratch)
    (stock : x<f.banks.width.base) (table : x<f.table) (dest : x<f.destination)
    (size : f.banks.width.base+edges≤f.source) :
    f.output (ReserveUse.output a f.banks reserve site debit (checkedOut C flag m)) e ci cj x =
      checkedOut C flag m x :=
  (f.frame _ e ci cj x stock table dest size).trans (ReserveUse.frame a f.banks reserve site debit _ x
    (Or.inl res) (Or.inl used) (Or.inl scratch))

end Hierarchy.ProtocolRAM.Calendar

end
end OAI
