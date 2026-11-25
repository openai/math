import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.DiagonalSourceReceivedRows
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape
import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # The signed receiving-cell roster at the real fragment bucket output -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder
open private tape_map from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape

/-- Changing the physical layout type or sampling new digits preserves the complete
ordered list of global cell numbers in the received directory. -/
theorem SameReportCells.numbers {l l' : ReportLayout} {cs : List (ReportCell l)} {ds : List (ReportCell l')}
    (h : SameReportCells cs ds) : cs.map ReportCell.number=ds.map ReportCell.number := by
  obtain ⟨rfl,same⟩ := h
  have ids (xs : List (ReportCell l)) : (eraseReportBits xs).map ReportCell.number=xs.map ReportCell.number :=
    tape_map (fun _ => false) _ (fun _ _ => rfl) xs 0
  exact (ids cs).symm.trans ((congrArg (List.map ReportCell.number) same).trans (ids ds))

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : SignedTaskArena.Layout) {team offsets ctl live ports bundles b description : ℕ}
    {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    (V : SignedPrep.Visits id pub mac s m) (owner : Fin bundles → Fin a.cube.cells)
    (header : Fin bundles → Packing.BottomReports.BundleHeader)
    {l : ReportLayout} {q : ReportCursor} {cs : List (ReportCell l)}
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "H" => a.openInputs team head offsets ctl live ports bundles b owner header
local notation3 (prettyPrint := false) "f" => FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)
local notation3 (prettyPrint := false) "cols" => a.controlRows team head offsets ctl live ports

/-- The original schedule's owner number remains in the real cell-control row
through report sampling and the stable bucket. No typed task output is used. -/
theorem Visits.owners_at_emission (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (who : ℕ → ℕ) (source : ∀ c : Fin a.cube.cells,readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=who c.val) :
    ∀ c : Fin a.cube.cells, (cols).owner (readings e.output) c.val=who c.val := by
  intro c
  let x := a.cube.hostDirectory+2*c.val
  obtain ⟨hh,lab,gw,ow,pair,host,_,_⟩ := a.cube.writer_order
  have lt := c.isLt
  have bankEnd := a.open_table_order.2.1
  have floor := room.primary
  have above := room.controlEnd
  have inside : x<a.cube.cellBank := by dsimp only [x]; omega
  have order := a.sparse_order room.cells
  have cover : (f).control=ctl := ptr
  have cut := e.original x (by rw [cover]; dsimp only [x]; omega) (.inl (inside.trans_le (order.1.trans order.2.1)))
  have frame : l.frame=head := seed.framePointer.symm
  have reports := ScheduleClock.report_return_before_cells seed alloc V.reports (x:=x) inside (by dsimp only [x]; omega)
  have image : readings V.controls.val.2.2=(H).image head (readings V.owned.val.2.2) :=
    ((OpenSuffix.run (H) ready).sound V.controls.property).2
  have clear := a.open_image_low owner header position x inside (by dsimp only [x]; omega)
  exact cut.trans ((congrArg Fin.val reports).trans ((congrFun image x).trans (clear.trans (source c))))

/-- If the original source lists these real cells in increasing global order,
each returned sparse row is the original cell with exactly that local ordinal. -/
theorem emitted_roster_order {label : ReportLayout} {cs : List (ReportCell label)}
    (rows : CellControlRows.Layout) (mem who : ℕ → ℕ) (C u : ℕ)
    (size : rows.cells=C) (processor : rows.team=u)
    (owners : ∀ c : Fin C, rows.owner mem c.val=who c.val)
    (listed : cs.map ReportCell.number=(List.range C).filter (fun c => decide (who c=u))) :
    ∃ roster : rows.before mem C=cs.length,
      ∀ i : Fin (rows.before mem C), (cs.get (Fin.cast roster i)).number=globalCell rows.toLayout mem i.val := by
  let ids := List.ofFn fun i : Fin (rows.before mem C) => globalCell rows.toLayout mem i.val
  have ord : ids=cs.map ReportCell.number := by
    rw [listed]
    have physical := globalCell_prefix rows.toLayout mem rows.cells le_rfl
    rw [size] at physical
    refine physical.trans ?_
    apply List.filter_congr
    intro c hc
    rw [owners ⟨c,List.mem_range.mp hc⟩,processor]
  have roster : rows.before mem C=cs.length := by simpa only [ids,List.length_ofFn,List.length_map] using congrArg List.length ord
  refine ⟨roster,fun i => ?_⟩
  have same := List.getElem_of_eq ord (i:=i.val) (by simpa only [ids,List.length_ofFn] using i.isLt)
  simpa only [ids,List.getElem_ofFn,List.getElem_map,List.get_eq_getElem,Fin.val_cast,Fin.eta] using same.symm


open Cube.Physical Cube.Physical.NativeAssignments DiagonalTallyCellReports.ReportDirectory

/-- The global identifier in the routed received roster equals the task builder's
cell at that compact ordinal. The first cast reindexes the actual scanner's
physical cells and the second one those of the selected source history. -/
theorem routed_emitted_ordinals {R bundles : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (label : Fin ar.cells → Cube.Label (ar.n+1) ar.header.d) (charts : Fin (R+1) → ReportLayout)
    (home : Fin bundles → Fin ar.cells) (bodies : Fin bundles → ReportBundle) (supply wire : ℕ → ℕ)
    (q : Routed (b:=ar.b) (s:=ar.s) owners) (u : Fin (R+1)) (rows : CellControlRows.Layout) (mem : ℕ → ℕ)
    {l : ReportLayout} (cs : List (ReportCell l)) :
    let issued := routedReceivedRows ar owners label charts home bodies supply wire q
    SameReportCells cs (issued.cells u) → rows.cells=ar.cells → rows.team=u.val →
    (∀ c : Fin ar.cells, rows.owner mem c.val=(owners q.1 (label c (chosen ar.b ar.s q.1))).val) →
    ∃ physical : rows.before mem ar.cells=cs.length, ∃ source : cs.length=(issued.cells u).length,
      ∀ i : Fin (rows.before mem ar.cells), (issued.order ⟨u,Fin.cast source (Fin.cast physical i)⟩).val=
        globalCell rows.toLayout mem i.val := by
  intro issued same size processor stored
  let who := routedOwnerWord ar owners label q
  have named : (issued.cells u).map ReportCell.number=(List.range ar.cells).filter (fun c => decide (who c=u.val)) := by
    change (((List.range ar.cells).filter _).map _).map _=_
    simp only [List.map_map,Function.comp_def,sourceCell]
    exact List.map_id _
  have names : ∀ c : Fin ar.cells, rows.owner mem c.val=who c.val :=
    fun c => (stored c).trans (routedOwnerWord_at ar owners label q c).symm
  obtain ⟨roster,pos⟩ := emitted_roster_order rows mem who ar.cells u.val size processor names named
  have len : cs.length=(issued.cells u).length := by simpa only [List.length_map] using congrArg List.length same.numbers
  refine ⟨roster.trans len.symm,len,fun i => ?_⟩
  exact ((issued.number u (Fin.cast roster i)).symm.trans (pos i))

/-- On a genuine physical report and stable fragment return, the received
selector's ordered cells are the actual sparse tasks. Only the original
owner word from the public owned scan is needed to recover their order. -/
theorem Visits.routed_roster_on_emission {R J : ℕ} (u : Fin (R+1)) (axis : Fin (a.cube.n+1))
    (owners : (Packet a.cube.n a.cube.header.d a.cube.header.blocks → Selector a.cube.n a.cube.K a.cube.h) →
      Fin a.cube.header.d → Fin (R+1))
    (label : Fin a.cube.cells → Cube.Label (a.cube.n+1) a.cube.header.d)
    (charts : Fin (R+1) → ReportLayout) (home : Fin J → Fin a.cube.cells) (bodies : Fin J → ReportBundle)
    (supply wire : ℕ → ℕ) (route : Routed (b:=a.cube.b) (s:=a.cube.s) owners)
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (source : ∀ c : Fin a.cube.cells, readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=
      (owners route.1 (label c (chosen a.cube.b a.cube.s route.1))).val)
    (teamIndex : team=u.val) :
    let issued := routedReceivedRows a.cube owners label charts home bodies supply wire route
    let count := (cols).before (readings e.output) a.cube.cells
    SameReportCells cs (issued.cells u) →
    ∃ physical : count=cs.length, ∃ source : cs.length=(issued.cells u).length,
      ∀ i : Fin count, (issued.order ⟨u,Fin.cast source (Fin.cast physical i)⟩).val=
        globalCell (cols).toLayout (readings e.output) i.val := by
  intro issued count same
  let who := routedOwnerWord a.cube owners label route
  have kept := V.owners_at_emission a owner header axis room position ready seed alloc e ptr who
    (fun c => (source c).trans (routedOwnerWord_at a.cube owners label route c).symm)
  exact routed_emitted_ordinals a.cube owners label charts home bodies supply wire route u (cols) (readings e.output)
    cs same rfl teamIndex (fun c => (kept c).trans (routedOwnerWord_at a.cube owners label route c))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
