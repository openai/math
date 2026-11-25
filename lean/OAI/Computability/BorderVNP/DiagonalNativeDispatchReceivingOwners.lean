import OAI.Computability.BorderVNP.DiagonalSparseReportOrdinals
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostRetention
import OAI.Computability.BorderVNP.CubeRoutePreparedEntry

/-! # Original receiving owners on the actual native sparse emitter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM DiagonalTallyAllocation DiagonalTallyCellReports FiniteEvaluator
open TeamContraction.ProcessorSlots FragmentRows TeamContraction BorderVNP.Cube TypedTaskBuilder
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

/-- The first column of the original directory passes through grouping,
report sampling and emission before the sparse tasks are dispatched. -/
theorem Visits.receivingOwners_at_native_emission (axis : Fin (a.cube.n+1))
    (room : a.OpenRoom head offsets ctl live ports bundles (2^b) w)
    (position : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after (a.cube.cellWriter head ctl axis) l cs q)
    {fit : (f).Fits w (readings V.reports.val.2.2)} {cells : a.fragments.cells=(f).cells}
    (e : SparseEmission a f V.reports.val.2.2 fit cells) (ptr : readings V.reports.val.2.2 (head+92)=ctl)
    {R : ℕ} {profile initial written : ℕ → ℕ}
    (entry : NativeEntry a.cube head ctl axis R profile initial written)
    (keep : CubeAllocation.HostRetention a.cube head initial written (readings V.owned.val.2.2)) :
    ∀ c : Fin a.cube.cells, (cols).owner (readings e.output) c.val =
      (a.cube.receivingOwner head axis R profile c.val).val := by
  apply V.owners_at_emission a owner header axis room position ready seed alloc e ptr
    (fun j => (a.cube.receivingOwner head axis R profile j).val)
  intro c
  obtain ⟨scheduled,_,image⟩ := entry.image
  have atWord := (image.hostRows c.val c.isLt).1
  have sized := c.isLt
  obtain ⟨_,labels,weights,owners,pair,host,_,_⟩ := a.cube.writer_order
  exact (keep.tables _ (by omega) (by omega)).trans (by simpa only [Nat.mul_comm 2 c.val] using atWord)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
