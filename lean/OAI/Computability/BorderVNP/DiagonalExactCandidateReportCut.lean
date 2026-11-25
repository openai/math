import OAI.Computability.BorderVNP.DiagonalReportCutLayoutCast

/-! # A report proposal on the concrete common chart of a returned team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM DiagonalTallyCellReports RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep

variable {T C : ℕ} {charts : Fin T → ReportLayout} (R : ReceivedRows charts C)
    {l l' : ReportLayout}

/-- Regard the actual returned directory as a directory on the selected
common report layout. -/
def onCommonChart (common : charts=fun _ => l) : ReceivedRows (fun _ : Fin T => l) C := common ▸ R

/-- The original source assignment on each returned team after recognizing
its common report layout. -/
def onCommonProposal (common : charts=fun _ => l) (src : ∀ u, ReportAssignments (R.cells u)) :
    ∀ u, ReportAssignments ((R.onCommonChart common).cells u) := by
  subst charts
  exact src

/-- Both the chosen layout and the native frame equality preserve the tape
and the sparse continuation on the particular original report return. -/
theorem exactSourceCut (common : charts=fun _ => l) (localFrame : l=l')
    (src : ∀ u, ReportAssignments (R.cells u)) (u : Fin T) {w : ℕ} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w} (actual : Returns prepareCellReports pub mac s m)
    {cur : ReportCursor} {desc : ℕ} (read : ReportArgumentCut actual (src u) cur desc) :
    Nonempty (ReportArgumentCut actual
      ((R.onCommonChart common).assignmentsAtLayout localFrame (R.onCommonProposal common src) u) cur desc) := by
  subst charts
  exact ⟨R.cutAtLayout localFrame src u actual read⟩

/-- Transport the proposal along an equality of physical frame families,
keeping the observed native return fixed, then identify the public frame
on which its original selected team actually runs. -/
theorem sourceCutOnFrames {Frames : Type*} {shape : Frames → Fin T → ReportLayout}
    (directory : (fs : Frames) → ReceivedRows (shape fs) C) {physical uniform : Frames}
    (alignment : physical=uniform) (common : shape uniform=fun _ => l) (active : l=l')
    (src : ∀ u, ReportAssignments ((directory physical).cells u)) (u : Fin T) {w : ℕ} {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w} (actual : Returns prepareCellReports pub mac s m)
    {cur : ReportCursor} {description : ℕ} (cut : ReportArgumentCut actual (src u) cur description) :
    let rr := directory uniform
    let proposed := cast (congrArg (fun fs => (t : Fin T) → ReportAssignments ((directory fs).cells t)) alignment) src
    Nonempty (ReportArgumentCut actual
      ((rr.onCommonChart common).assignmentsAtLayout active (rr.onCommonProposal common proposed) u) cur description) := by
  subst uniform
  exact (directory physical).exactSourceCut common active src u actual cut

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
