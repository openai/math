import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.DiagonalNativeSelectorRoster
import OAI.Computability.BorderVNP.RoutingISASparseReportSources

/-! # Owners on the actual sparse emitter after the public greedy schedule -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder
open BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment RoutingISA.LocalRow

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


variable {r : ℕ} {A : Type} [Fintype A]
    {decl : LengthDeclaration a.cube.n a.cube.header.d}
    {group : Fin a.cube.header.d → Fin (r+1)}
    (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ)
local notation3 (prettyPrint := false) "choiceOwners" => greedyOwner r a.cube.b a.cube.s label recv incoming

/-- Pass directly from the actual public schedule and the observed returned
ownership to the original global rows of this particular sparse emitter.
The two scheduler memories enter only through their certified owner words. -/
theorem Visits.scheduledOwners_at_emission
    {family : TeamRows.Returns (Fin (r+1)) a.cube w} {rowBits : Symbols a.cube.header.d → List Bool}
    {assignment : NativeAssignments.Routed (b:=a.cube.b) (s:=a.cube.s) choiceOwners}
    (observed : ObservedOwned a.cube decl group family choiceOwners rowBits assignment)
    {prof assigned : ℕ → ℕ}
    (schedule : GroupWeights.ScheduleResult (weightLayout a.cube head decl.1.val) (teamLayout a.cube r) prof assigned)
    (image : GroupWeights.PhysicalImage (weightLayout a.cube head decl.1.val) prof a.cube.header.blocks
      a.cube.b a.cube.K a.cube.h decl label recv incoming)
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl decl.1) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    (source : ∀ c : Fin a.cube.cells, readings V.owned.val.2.2 (a.cube.hostDirectory+2*c.val)=(group (label c decl.1)).val) :
    ∀ c : Fin a.cube.cells, (cols).owner (readings e.output) c.val=ScheduleClock.scheduledCellOwner a.cube decl label assigned c := by
  let who (i : ℕ) := if h : i<a.cube.cells then (group (label ⟨i,h⟩ decl.1)).val else 0
  have real := V.owners_at_emission a owner header decl.1 room position ready seed alloc e ptr who
    (fun c => (source c).trans (by simp only [who,dite_eq_left c.isLt]))
  have legal : passesLengths a.cube.b a.cube.s assignment.1 decl := (passesLengths_iff ..).mpr observed.observed.1.symm
  intro c
  have selected := (greedyOwner_stored schedule assignment.1 legal label recv incoming image (label c decl.1)).trans
    (congrArg (fun h => (h (label c decl.1)).val) observed.allocation)
  have localOwner := real c
  simp only [who,dite_eq_left c.isLt] at localOwner
  exact localOwner.trans selected.symm

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
