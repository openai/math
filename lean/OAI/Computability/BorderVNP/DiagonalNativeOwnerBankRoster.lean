import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster
import OAI.Computability.BorderVNP.DiagonalNativeSelectorRoster
import OAI.Computability.BorderVNP.DiagonalProducedRoster

/-! # The reached selector's cell owners on the native positive prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CellPacket CellPacket.Supplement.Batch TypedTaskBuilder
open BorderVNP.Cube Physical FiniteEvaluator DiagonalTallyCellReports PositiveTeam

variable {w n : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {Site : Type}

/-- The actual two-word cell writer shares the checked native scheduler's label,
digit, and owner fields. The layout proof uses the length-only cube address order. -/
theorem cell_schedule_layout (ar : CubeArena.Layout) (head ctl R : ℕ) (axis : Fin (ar.n+1)) :
    CellBanks.ScheduleLayout (ar.cellWriter head ctl axis) (LocalRow.weightLayout ar head axis.val) (LocalRow.teamLayout ar R) := by
  obtain ⟨_,labels,owner,_,_,_,_,_⟩ := ar.writer_order
  have totals : ar.groupWeights≤ar.teamTotals := Nat.le_add_right ..
  exact ⟨rfl,rfl,rfl,rfl,rfl,labels,labels.trans totals,labels.trans owner⟩

variable {a : SignedTaskArena.Layout} {ctl u v k R team offsets live ports bundles b description : ℕ}
    {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {input orig written : ℕ → ℕ}
    {l : ReportLayout} {q : ReportCursor} {cs : List (ReportCell l)}
    {A : Type*} [Fintype A] (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (width : A → ℕ)
    (select : Packet a.cube.n a.cube.header.d a.cube.header.blocks → Selector a.cube.n a.cube.K a.cube.h)
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)

set_option quotPrecheck false
local notation "head" => readings pub 0
local notation "H" => a.openInputs team head offsets ctl live ports bundles b owner header
local notation "rows" => a.controlRows team head offsets ctl live ports
local notation "banks" => a.cube.cellWriter head ctl decl.1
local notation "weights" => LocalRow.weightLayout a.cube head decl.1.val
set_option quotPrecheck false in
local notation "actualOwner" => fun c : Fin a.cube.cells =>
  greedyOwner R a.cube.b a.cube.s label recv width select (label c (chosen a.cube.b a.cube.s select))

set_option maxHeartbeats 1200000 in
/-- The actual complete positive preparation returns a directory of all global
cells whose first column contains the selector-dependent greedy owner. Its
source includes the received physical declaration, the original report headers
and the sparse input on this very prefix's native task-builder output. -/
theorem selected_ownerTable_on_visits (V : SignedPrep.Visits id pub mac s m)
    (passing : passesLengths a.cube.b a.cube.s select decl)
    (physical : GroupWeights.PhysicalImage weights input a.cube.header.blocks a.cube.b a.cube.K a.cube.h decl label recv width)
    (entry : NativeEntry a.cube head ctl decl.1 R input orig written)
    (kept : CubeAllocation.HostRetention a.cube head orig written (readings V.owned.val.2.2))
    (openRoom : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (words : ∀ i : Fin 37, readings V.reports.val.2.2 (ctl+i.val)=a.controls i.val)
    (cables : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (raw : readings V.reports.val.2.2 (head+9) ≤ a.cube.maxRows)
    (cells : readings V.reports.val.2.2 (head+11)=a.cube.cells) (high : a.endAddress w u v k < 2^w)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let parts := (argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    let old := readings parts.1.val.2.2
    ∀ src : SparseCallInput pub parts.2.1.val.2.2, ProducedRoster a rows old p geom extra src →
    OwnerTable pub (SignedPrep.visitsEquiv id pub mac s m V).val.2.2 ⟨team,a.before.limit,a.cube.cells⟩
      (ownerWord actualOwner) := by
  intro parts old src data
  obtain ⟨scheduled,sched,held⟩ := owner_bank_on_visits owner header V entry kept openRoom position ready seed alloc
    place fit ptr words cables raw cells high
  have roster := ownerTable_on_arguments V.arguments rows a ctl p geom extra src rfl data.fields data.room data.span
    data.frameLow.1 data.frameLow.2 data.callsHigh.1 data.callsHigh.2 data.merge data.count data.layout
    data.globals data.widths data.early rfl le_rfl
  rw [SignedPrep.visitsEquiv_outState id pub mac V]
  exact OwnerTable.from_selected_bank (pub := pub) (m := V.arguments.val.2.2)
    (g := weights) (teams := LocalRow.teamLayout a.cube R) («banks» := banks)
    (orig := input) (scheduled := scheduled) (decl := decl)
    select passing label recv width (cell_schedule_layout a.cube head ctl R decl.1) sched physical
    (rows).toLayout old team a.before.limit rfl rfl rfl rfl held roster

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
