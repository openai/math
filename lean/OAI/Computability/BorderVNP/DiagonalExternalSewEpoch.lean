import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry
import OAI.Computability.BorderVNP.DiagonalSiteExecution

/-! # Actual site-to-site execution retains every external attachment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Cover Epoch Epoch.Round Adaptive Packing Catalog CellEntries
open scoped Classical BorderVNP.Epoch.Cube

variable {D : ℕ} {P : Type} {bits : P → ℕ}

/-- Identify two recorded presentations of the same physical layout. -/
def Retains.ofEq {N M : Network D P bits} (h : N = M) : Retains N M :=
  h ▸ Retains.id N

variable {m rounds k : ℕ} [NeZero D] {E : Type} [Field E] [Fintype P] {e : PaidIdentity E D m}
    {h H ν : ℝ} {path : StagePath rounds e (Cube D) h H ν} {C : Fin rounds → ℕ}
    {last high : ℕ} {hk : 0 < k} {machine : SiteMachine path C last high hk P bits}
    {low : ℕ} {L weight error A Cout : ℝ} {cap : ℕ} {hh : 0 < h}
    {input : Fin (k^rounds) → Pack D P bits E} {route : ∀ i, SiteRoutes (input i) (Cube D) high L}
    (run : SiteExecution (low := low) machine hh input route weight error A Cout cap)

/-- At installation each original host remains as the old endpoint of
the actual geodesic subdivision used by this site execution. -/
noncomputable def installedHosts (i : Fin (k^rounds)) :
    Retains (input i).layout (run.flat i).val.pack.layout := by
  let data := run.initialSites i
  let original := Retains.ofEq (congrArg Pack.layout (run.originalPack i).symm)
  let stored := Retains.ofEq (congrArg (fun p => p.pack.layout) data.realizes.symm)
  exact original.trans ((Retains.subdivide data.pack.layout (data.routes.routes h)).trans stored)

/-- Every output of the actual site epoch retains the original input
attachment at the row-major leaf number of the site machine. -/
noncomputable def epochHosts (j : Fin run.expansion.terms) :
    Retains (parallelPacks input).layout (run.expansion.pack j).layout :=
  (Retains.parallel (installedHosts run)).trans
    (terminalHosts machine.F (SiteReplay.storage machine) run.flat (run.enum j))

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
