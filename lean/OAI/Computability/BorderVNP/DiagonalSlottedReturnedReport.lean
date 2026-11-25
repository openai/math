import OAI.Computability.BorderVNP.DiagonalReportSourcePlacement
import OAI.Computability.BorderVNP.CubeRouteEmitterInputs

/-! # The slotted row and the held report on one owner return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube SignedTaskArena Packing

/-- The earlier slotted writer and the retained report refer to the same
published memory once the owner return identifies the public registers. -/
def SlottedWriter.onReportReturn {w base : ℕ} {a : Layout} {d : Directory.Layout}
    {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {pub active : Arg → Word w}
    {slotted output : Memory w} {I : Type*} [Fintype I]
    {cell : I → Fin a.cube.cells} {key : I ↪ ℕ} {width : I → ℕ}
    (writer : SlottedWriter a.cube d pp lp pins pub slotted base cell key width)
    (publicEq : active=pub)
    (stored : output=Directory.ISA.publish slotted (pub 0).val base (d.directory pp lp))
    {written result : ℕ → ℕ}
    (held : ReportWords a (active 0).val (readings output) written result true) :
    (SlottedWriter a.cube d pp lp pins active slotted base cell key width) ×'
      (ReportWords a (active 0).val (readings (Directory.ISA.publish slotted (active 0).val base (d.directory pp lp)))
        written result true) := by
  subst active
  subst output
  exact ⟨writer,held⟩

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
