import OAI.Computability.BorderVNP.DiagonalCandidateReportTaskImage

/-! # Transferring the returned source geometry to the original selected site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Packing VPVNP.BurstRAM

/-- Task, source directory, frame and original RAM determine the full packet
read at the physical site of a retained lookup. -/
theorem ReportTaskImage.atSite {w : ℕ} {task selected : SignedTaskArena.Layout}
    {directory installed : Directory.Layout} {frame base origin : ℕ} {site physical : Memory w}
    (same : task=selected) (dirs : directory=installed) (pointer : frame=base)
    (retained : site=physical)
    (packet : ReportTaskImage selected installed.entries (installed.teams*installed.sites)
      base origin w (readings physical)) :
    ReportTaskImage task directory.entries (directory.teams*directory.sites)
      frame origin w (readings site) := by
  cases same
  cases dirs
  cases pointer
  cases retained
  exact packet

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
