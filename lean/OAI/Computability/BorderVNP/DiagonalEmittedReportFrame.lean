import OAI.Computability.BorderVNP.DiagonalFrozenPostReportWords
import OAI.Computability.BorderVNP.DiagonalFrozenPrefixFinishCalibration
import OAI.Computability.BorderVNP.FragmentDirectoryInputArena

/-! # The compact report frame recovered at the actual sparse emission -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Evaluator.ScheduleClock TeamContraction.ProcessorSlots

variable {w : ℕ} {task : SignedTaskArena.Layout} {pub : Arg → Word w} {m : Memory w}
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "f" => Layout.fromFrame ((pub 0).val) (readings m)

/-- The real fragment return and the installed scalar controls recover the
complete report frame. The row count is measured on the original report RAM. -/
theorem SparseEmission.issuedFrame
    {fit : (Layout.fromFrame ((pub 0).val) (readings m)).Fits w (readings m)}
    {cells : task.fragments.cells=(Layout.fromFrame ((pub 0).val) (readings m)).cells}
    (e : SparseEmission task f m fit cells)
    (A : StartupArena) {ctl offsets reserve axes groups cap width query guesses gates rows : ℕ}
    (addresses : task.FinishAddresses A ctl reserve axes groups cap width w query guesses gates)
    (atFrame : head=A.frame)
    (geometry : SparseGeometry task f offsets ctl)
    (words : ∀ i : Fin 37, readings m (ctl+i.val)=task.controls i.val)
    (count : (f).count=rows) : IssuedReportFrame task pub m offsets ctl rows := by
  have low : head+112 ≤ ctl := by
    rw [atFrame]
    apply le_trans _ addresses.controlAbove
    unfold StartupArena.next StartupArena.hbase StartupArena.ibase StartupArena.broadcastBase StartupArena.dense
    omega
  let actual := FragmentDirectoryInput.ofArena pub m task fit geometry.control words low
    (geometry.controller.trans (arena_order task).1) e.cables e.raw cells.symm addresses.endFit
  exact ⟨actual,fit,count,rfl,cells,e.cables,rfl,words,geometry⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
