import OAI.Computability.BorderVNP.DiagonalRegisteredReportCut
import OAI.Computability.BorderVNP.DiagonalExactCandidateReportCut
import OAI.Computability.BorderVNP.DiagonalPrefixFinishRun

/-! # Keeping a registered source prefix while reindexing its report frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart.jointReportCutAt

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator SignedPrep CellMacro.Generator
open _root_.OAI.Computability.BorderVNP.Cube Physical.NativeAssignments Physical.NativeLedger DiagonalTallyCellReports

/-- The registered decoder's report observation retains the original native
prefix when the report roster is rewritten along the uniform frame equality. -/
theorem sourceOnFrames {R n w axes b h K s C : ℕ} {X Frames : Type} {gen : Fragment IO}
    {id : TableEntry axes b h K s → ℕ} {teams : X → Fin (R+1) → PositiveTeam id gen n w}
    {z : JointBeforeCells teams} {u : Fin (R+1)} {shape : Frames → Fin (R+1) → ReportLayout}
    (directory : (f : Frames) → ReceivedRows (shape f) C) {physical uniform : Frames}
    (alignment : physical=uniform) {l l' : ReportLayout} (common : shape uniform=fun _ => l) (active : l=l')
    (src : ∀ k, ReportAssignments ((directory physical).cells k))
    (real : jointReportCutAt teams z u (src u)) :
    let rr := directory uniform
    let proposed := cast (congrArg (fun f => (k : Fin (R+1)) → ReportAssignments ((directory f).cells k)) alignment) src
    ∃ cur desc, Nonempty (ReportArgumentCut (prefixVisits (teams z.1 u) (z.2 u)).reports
      ((rr.onCommonChart common).assignmentsAtLayout active (rr.onCommonProposal common proposed) u) cur desc) := by
  obtain ⟨cur,desc,cut⟩ := real
  exact ⟨cur,desc,ReceivedRows.sourceCutOnFrames directory alignment common active src u
    (prefixVisits (teams z.1 u) (z.2 u)).reports cut.some⟩


/-- The report return on the original team, indexed by its physical and selected frame families. -/
def FrameObservation {R n w axes b h K s C : ℕ} {X Frames : Type} {gen : Fragment IO}
    {id : TableEntry axes b h K s → ℕ} {teams : X → Fin (R+1) → PositiveTeam id gen n w}
    {z : JointBeforeCells teams} {u : Fin (R+1)} {shape : Frames → Fin (R+1) → ReportLayout}
    (directory : (f : Frames) → ReceivedRows (shape f) C) {physical uniform : Frames}
    (alignment : physical=uniform) {l l' : ReportLayout} (common : shape uniform=fun _ => l) (active : l=l')
    (src : ∀ k, ReportAssignments ((directory physical).cells k))
 : Prop :=
    let rr := directory uniform
    let proposed := cast (congrArg (fun f => (k : Fin (R+1)) → ReportAssignments ((directory f).cells k)) alignment) src
    ∃ cur desc, Nonempty (ReportArgumentCut (prefixVisits (teams z.1 u) (z.2 u)).reports
      ((rr.onCommonChart common).assignmentsAtLayout active (rr.onCommonProposal common proposed) u) cur desc)

/-- The registered physical scanner provides the observed return at both frame indices. -/
theorem frameObservation {R n w axes b h K s C : ℕ} {X Frames : Type} {gen : Fragment IO}
    {id : TableEntry axes b h K s → ℕ} {teams : X → Fin (R+1) → PositiveTeam id gen n w}
    {z : JointBeforeCells teams} {u : Fin (R+1)} {shape : Frames → Fin (R+1) → ReportLayout}
    (directory : (f : Frames) → ReceivedRows (shape f) C) {physical uniform : Frames}
    (alignment : physical=uniform) {l l' : ReportLayout} (common : shape uniform=fun _ => l) (active : l=l')
    (src : ∀ k, ReportAssignments ((directory physical).cells k))
    (real : jointReportCutAt teams z u (src u)) :
    FrameObservation (teams:=teams) (z:=z) (u:=u) directory alignment common active src :=
  sourceOnFrames directory alignment common active src real

end TeamContraction.ProcessorSlots.BootedPinStart.jointReportCutAt

end BorderVNP
end Computability
end OAI
