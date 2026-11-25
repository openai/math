import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenSuffix
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Signed addresses of the two directory writers after the host scatter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Packing DiagonalTallyAllocation FiniteEvaluator

variable (t : Layout)

/-- Pointers from signed controls 18–21 and the true frame bundle and cell counts. -/
noncomputable def Layout.bundleLayout (frame control bundles : ℕ) : BundleDirectory.Layout :=
  ⟨frame,control,t.cube.cells,bundles,t.before.ranges,t.before.bundleTable,t.p.bundlePayload,t.p.bundleInverse⟩

/-- Native per-owned-cell controls use the same geometry, receiving banks, and
report reservations as the subsequent signed task and scanner. -/
noncomputable def Layout.controlRows (team frame offsets control live ports : ℕ) : CellControlRows.Layout :=
  { t.tasks team frame offsets control with
    ports := ports, live := live, four := t.before.four, supplemental := t.before.supplement,
    stride := t.before.bound.supplementStride, counters := t.before.counters, merged := t.before.merged,
    reportWords := 1+t.before.bound.gadgets*(1+t.before.bound.countWidth), six := t.before.six,
    ranges := t.before.ranges }

/-- The bundle groups of the fixed native suffix follow the geometry sort's stable
source order, including empty cells. -/
noncomputable def Layout.openInputs (team frame offsets control live ports bundles b : ℕ)
    (owner : Fin bundles → Fin t.cube.cells) (header : Fin bundles → BottomReports.BundleHeader) : OpenSuffix.Inputs :=
  ⟨t.bundleLayout frame control bundles,BundleDirectory.groups owner header,2^b,
    t.controlRows team frame offsets control live ports⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
