import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster
import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.DiagonalProducedRoster
import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows

/-! # The real call owner table after the emitted sparse and typed arguments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder
open CellDispatch ScheduleClock

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

/-- All global owners selected by the physical scanner survive the genuine fragment, supplemental,
compressed and typed task writers. The intermediate owner table and the produced roster use the
same chronological fragment return for the very same prefix. -/
theorem Visits.ownerTable_after_emission {teams : ℕ} (who : Fin a.cube.cells → Fin teams)
    (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (source : ∀ c : Fin a.cube.cells, readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=(who c).val)
    {Site : Type} (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let parts := (argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
    e.output=parts.1.val.2.2 → ∀ (packet : SparseCallInput pub parts.2.1.val.2.2),
      ProducedRoster a cols (readings e.output) placed geom extra packet →
      OwnerTable pub (visitsEquiv id pub mac s m V).val.2.2 ⟨team,a.before.limit,a.cube.cells⟩
        (PositiveTeam.ownerWord who) := by
  intro parts banked packet produced
  have observed := V.owners_at_emission a owner header axis room position ready seed alloc e ptr (PositiveTeam.ownerWord who)
    (fun c => (source c).trans (by simp only [PositiveTeam.ownerWord, dite_eq_left c.isLt]))
  rw [banked] at observed produced
  have roster := ownerTable_on_arguments V.arguments (cols) a ctl placed geom extra packet rfl
    produced.fields produced.room produced.span produced.frameLow.1 produced.frameLow.2
    produced.callsHigh.1 produced.callsHigh.2 produced.merge produced.count produced.layout
    produced.globals produced.widths produced.early rfl le_rfl
  rw [visitsEquiv_outState id pub mac V]
  exact ⟨roster.frame,fun i hi => (roster.atRow i hi).trans (observed ⟨i,hi⟩)⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
