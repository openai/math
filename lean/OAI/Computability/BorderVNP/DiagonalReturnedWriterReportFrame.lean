import OAI.Computability.BorderVNP.DiagonalEmittedReportFrame
import OAI.Computability.BorderVNP.DiagonalSignedFragmentPublication
import OAI.Computability.BorderVNP.CubeRouteCompleteSchedule

/-! # Compacted row count of the same returned writer and report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Evaluator ScheduleClock SignedTaskArena TeamContraction.ProcessorSlots
open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical

variable {w teams : ℕ} {task : SignedTaskArena.Layout} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {original reported later : Memory w}
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "f" => Layout.fromFrame ((pub 0).val) (readings reported)

set_option maxHeartbeats 900000 in
/-- A report and its retained writer agree on the number of populated raw
rows in their common frame, including reports with arbitrary guessed bits. -/
theorem SparseEmission.issuedWriterFrame
    {fit : (Layout.fromFrame ((pub 0).val) (readings reported)).Fits w (readings reported)}
    {cells : task.fragments.cells=(Layout.fromFrame ((pub 0).val) (readings reported)).cells}
    (e : SparseEmission task f reported fit cells)
    (A : StartupArena) {ctl offsets reserve axes groups cap width query guesses gates : ℕ}
    (addresses : task.FinishAddresses A ctl reserve axes groups cap width w query guesses gates)
    (atFrame : head=A.frame)
    (geometry : SparseGeometry task f offsets ctl)
    (controls : ∀ i : Fin 37, readings reported (ctl+i.val)=task.controls i.val)
    {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {owner : ℕ → Fin (teams+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
    {group : Fin task.cube.header.d → Fin (teams+1)} {pinLayout : Pins.Layout}
    {r s : Bank w} {events : List (TeamRAM.Event w)}
    (W : WriterHistory task.cube.n (Tally.selectorWidth task.cube.n task.cube.K task.cube.h) pub mac r original events s later)
    (done : ReturnedWriters task.cube dir pp lp owner decl group pinLayout W)
    {before : ℕ → ℕ} (words : ReportWords task head (readings original) before (readings reported) true) :
    IssuedReportFrame task pub reported offsets ctl (dir.directory pp lp).length := by
  apply e.issuedFrame A addresses atFrame geometry controls
  have field := words.frame_word 9 (by decide) (by decide) (by decide) (by decide) (fun _ => by decide)
  have same := done.low (head+9) (by have := words.primary; omega)
  exact field.trans ((congrArg Fin.val same).symm.trans done.emission.demand.count.symm)

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
