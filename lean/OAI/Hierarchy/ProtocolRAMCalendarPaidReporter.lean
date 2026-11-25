import OAI.Hierarchy.ProtocolRAMNativePaidReporter
import OAI.Hierarchy.ProtocolRAMFinalInstalledWidths
import OAI.Hierarchy.ProtocolRAMCalendarWhole

namespace OAI
/-! # The final priced graph from the actual archived installations and terminal stocks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {W q d r edges n count : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

/-- Read the installed credits left by the very same temporal event that issued
its toll receipt. Every later physical stage and the scalar guard preserve the word. -/
theorem archived_credit (C : Chart W q d) (flag : ℕ) (m : Memory W) (pre post : List Event)
    (event : Attempt) (split : events C.mesh=pre++(.attempt event)::post)
    (a : StockCommit.Area) (s : StockCommit.Sources) (g : StockCommit.LabelSource) (b : Batch q d)
    (i : Fin a.occurrences) (v : Memory W) (physical : C.commit event=StockCommit.pricedSegment a s g W b)
    (snap : PurchaseStage.postOutput (C.layout event) (repair C event) (prepared C event (run C pre m))=v)
    (ready : (StockCommit.pricedSegment a s g W b).ready v) (board : StockCommit.EventBoard (StockCommit.fresh a s) W)
    (eligible : mounted C post (after C (.attempt event) (run C pre m)))
    (keep : ∀x∈post,protected C (a.direct+i.val) x) (apart : a.direct+i.val≠flag) :
    let st := StockCommit.fresh a s
    let u := StockCommit.stageInput a s g v
    (checkedOut C flag m (a.direct+i.val)).val=if RepairHistogram.kind (goods:=a.goods) st.plan.bank st.columns u i=none
      then RepairHistogram.installedBits st.columns u i else 0 := by
  rw [archived_word C flag _ m pre post _ split eligible keep apart,after,physical,snap,StockCommit.priced_after]
  let st := StockCommit.fresh a s
  let u := StockCommit.stageInput a s g v
  have mounted : (st.native W a.rows b).ready u := ready.2.2
  exact (st.read_direct b u i mounted board.chargeFits board.order (board.hit b u mounted i) board.bound (board.keep i)).1

def paidSource (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive)
    (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ) (m : Memory W) :=
  ReserveUse.output a f.banks reserve site debit (PaidWidths.output f.banks.width edges src ss (checkedOut C flag m))

attribute [local irreducible] Procedure.Exec

omit [Fintype I] [Fintype J] in
theorem paidReporter_exec (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory W)
    (ready : mounted C (events C.mesh) m) (fit : (historyFlag C (events C.mesh)).Fits W flag) (room : flag+1<2^W)
    (widthRoom : f.banks.width.base+edges<2^W) (paid : PaidWidths.Mounted f.banks.width edges src ss (checkedOut C flag m))
    (arch : ReserveUse.Mounted a f.banks reserve site debit (PaidWidths.output f.banks.width edges src ss (checkedOut C flag m)))
    (sink : f.Mounted (paidSource C flag f src ss a reserve site debit m) e ci cj) :
    (paidReporter C flag f src ss a count n reserve).Exec m (f.output (paidSource C flag f src ss a reserve site debit m) e ci cj)
      (paidReporterTime C f ss a count n reserve) := by
  exact Procedure.Exec.then
    (Procedure.Exec.then
      (Procedure.Exec.then (checked_exec C flag m ready fit room)
        (PaidWidths.exec f.banks.width src ss _ widthRoom paid))
      (ReserveUse.exec a f.banks reserve site debit _ arch))
    (f.exec _ e ci cj sink)

/-- One physical charged edge row contains all paid installations (including
broadcast and earlier overflow), the terminal residual core stock, and the unused
external catalyst return. Its initial installed width is computed from history. -/
theorem paidReporter_width (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory W) (e : Fin edges)
    (fits : ∀s∈ss,s.Fits f.banks.width edges src W) (width : edges≤f.banks.width.size) (countFit : edges≤2^W)
    (outside : f.banks.width.base+edges≤f.banks.reserved.base ∧ f.banks.width.base+edges≤f.banks.used.base ∧
      f.banks.width.base+edges≤a.scratch) (source : f.banks.width.base+edges≤f.source)
    (room : let original := checkedOut C flag m
      let final := paidSource C flag f src ss a reserve site debit m
      PaidWidths.total ss original e + (routeLoad core (fun i=>RouteSettlement.actual f.banks.stock final (ci i)) e+
        routeLoad center (fun j=>RouteSettlement.actual f.banks.reserved final (cj j)-RouteSettlement.actual f.banks.used final (cj j)) e)<2^W) :
    let original := checkedOut C flag m
    let final := paidSource C flag f src ss a reserve site debit m
    (f.terminalRows final enum ci cj e).width=PaidWidths.total ss original e+
      routeLoad core (fun i=>RouteSettlement.actual f.banks.stock final (ci i)) e+
      routeLoad center (fun j=>RouteSettlement.actual f.banks.reserved final (cj j)-RouteSettlement.actual f.banks.used final (cj j)) e := by
  intro original final
  have retained : final (f.banks.width.base+e.val)=PaidWidths.output f.banks.width edges src ss original (f.banks.width.base+e.val) :=
    ReserveUse.frame a f.banks reserve site debit _ _ (.inl (by have := e.isLt;omega))
      (.inl (by have := e.isLt;omega)) (.inl (by have := e.isLt;omega))
  have installed : (final (f.banks.width.base+e.val)).val=PaidWidths.total ss original e :=
    (congrArg Fin.val retained).trans (PaidWidths.read f.banks.width src ss original e fits (by change PaidWidths.total ss original e+_<2^W at room;omega))
  have read := f.terminal_width final enum ci cj e width countFit source
    (by simpa only [installed] using room)
  simpa only [installed] using read

/-- Text cost is independent of each slice length. It includes its archive row
expression and the constant fourteen-label weighted-scatter procedure. -/
theorem paid_text (W edges src : ℕ) (bank : Bank) (ss : List PaidWidths.Slice) :
    text (PaidWidths.native W edges src bank ss)=30+
      (ss.map (fun s=>rowText (RepairHistogram.pair (s.columns bank edges))+22)).sum := by
  have inner : text (PaidWidths.scans W edges src bank ss)=15+
      (ss.map (fun s=>rowText (RepairHistogram.pair (s.columns bank edges))+22)).sum := by
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      have fixed : text (ProtocolRAMWeightedScatter.program W src s.count)=22 := rfl
      simp only [PaidWidths.scans,RepairHistogram.code,text_seq,text_scan,fixed,ih,List.map_cons,List.sum_cons]
      omega
  rw [PaidWidths.native,text_seq,inner]
  change 15+(15+_)=30+_
  omega

theorem paidReporter_text (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (paidReporter C flag f src ss a count n reserve)=
      15+((events C.mesh).map (eventText C)).sum+rowText (historyFlag C (events C.mesh))+
      (30+(ss.map (fun s=>rowText (RepairHistogram.pair (s.columns f.banks.width edges))+22)).sum)+
      (listText (ReserveUse.columns a f.banks count n reserve)+22)+sinkText f := by
  have fixed : text (ProtocolRAMWeightedScatter.program W a.scratch n)=22 := rfl
  simp only [paidReporter,text_seq,text_checked,paid_text,ReserveUse.native,text_passes,fixed,text_sink]

omit [Fintype I] [Fintype J] in
theorem paidReporter_run (C : Chart W q d) (flag : ℕ) (f : Sink r edges) (src : ℕ) (ss : List PaidWidths.Slice)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (m : Memory W) (state : Word W)
    (ready : mounted C (events C.mesh) m) (order : separated C (events C.mesh))
    (fit : (historyFlag C (events C.mesh)).Fits W flag) (room : flag+1<2^W)
    (widthRoom : f.banks.width.base+edges<2^W) (paid : PaidWidths.Mounted f.banks.width edges src ss (checkedOut C flag m))
    (arch : ReserveUse.Mounted a f.banks reserve site debit (PaidWidths.output f.banks.width edges src ss (checkedOut C flag m)))
    (sink : f.Mounted (paidSource C flag f src ss a reserve site debit m) e ci cj)
    (lo : flag<f.banks.width.base ∧ flag<f.banks.reserved.base ∧ flag<f.banks.used.base ∧ flag<a.scratch ∧ flag<f.table ∧ flag<f.destination) :
    let A := machine (paidReporter C flag f src ss a count n reserve) (flag:Word W)
    let out := f.output (paidSource C flag f src ss a reserve site debit m) e ci cj
    ∃t≤paidReporterTime C f ss a count n reserve+2,∃done,advance A.program t (A.program.start state) m=some (done,out) ∧
      A.program.step done=.finish (some (out flag)) ∧ (out flag=0 ↔ admissible C (events C.mesh) m) := by
  let final := paidSource C flag f src ss a reserve site debit m
  have runs : (paidReporter C flag f src ss a count n reserve).Exec m (f.output final e ci cj) (paidReporterTime C f ss a count n reserve) :=
    paidReporter_exec C flag f src ss a reserve site debit e ci cj m ready fit room widthRoom paid arch sink
  obtain ⟨t,ht,done,run,halt⟩ := machine_run _ (flag:Word W) state m _ _ runs
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)] at halt
  refine ⟨t,ht,done,run,halt,?_⟩
  obtain ⟨fWidth,fReserve,fUsed,fScratch,fTable,fDestination⟩ := lo
  rw [f.frame final e ci cj flag fWidth fTable fDestination sink.sourceRoom]
  change (ReserveUse.output a f.banks reserve site debit _ flag=0 ↔ _)
  rw [ReserveUse.frame _ _ _ _ _ _ flag (.inl fReserve) (.inl fUsed) (.inl fScratch),
    PaidWidths.frame _ _ _ _ _ flag (fun s hs=>(paid s hs).1) fWidth]
  exact checked_read C flag m ready order (by have := sink.wide;omega)

end Hierarchy.ProtocolRAM.Calendar

end
end OAI
