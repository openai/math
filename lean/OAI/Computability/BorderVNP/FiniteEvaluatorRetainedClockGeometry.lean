import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedReportSeed
import OAI.Computability.BorderVNP.FiniteEvaluatorScalarReportDirectory
import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits
import OAI.Computability.BorderVNP.PackedRoutingOutputs
import OAI.Computability.BorderVNP.CellPacketGeometryRate

/-! # The public geometry counts used by the finite post-routing clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator Packing BorderVNP.Cube VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator ScheduleClock
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

variable (a : Layout) {team frame offsets control live ports bundles b : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (hdr : Fin bundles → BottomReports.BundleHeader)
local notation "H" => a.openInputs team frame offsets control live ports bundles b owner hdr

/-- The published label chooser and later host scan use precisely the same
cable count. The three remaining opening-loop lengths fit in the physical
word array of the retained emitter, including its private controls and tail. -/
theorem Layout.retained_open_counts {initial written ready : ℕ → ℕ}
    (keep : CubeAllocation.HostRetention a.cube frame initial written ready)
    (liveCount controls packetWords : ℕ) :
    let out := a.cube.cables*3+(RoutingOutputs.count a.cube.cables a.cube.cells bundles liveCount+
      ((a.cube.cells+(bundles+a.cube.cells))+(controls+packetWords)))
    (HostScatter.Layout.fromFrame frame ready).count=(LabelIndex.layout frame initial).cableCount ∧
      (H).bundles.cells ≤ out ∧ (H).bundles.bundles ≤ out ∧ (H).control.cells ≤ out ∧ packetWords ≤ out := by
  intro out
  have base := keep.primary
  refine ⟨keep.lower (frame+7) (by omega) (by omega) (by omega),?_⟩
  change a.cube.cells ≤ out ∧ bundles ≤ out ∧ a.cube.cells ≤ out ∧ packetWords ≤ out
  dsimp only [out]
  omega

/-- The physical task columns lie in the same public power-of-two buffer as
the actual packet geometry template, including the degenerate empty grid. -/
theorem Layout.retained_cell_fit {E I Orig : Type} {s : ℕ}
    (T : CellPacketGeometry.LiveWords.Template E I Orig s a.cube.cells) (team frame offsets control : ℕ) :
    (a.tasks team frame offsets control).cells ≤ 2^T.publicDepth := by
  change a.cube.cells ≤ 2^T.publicDepth
  exact (Nat.le_add_right a.cube.cells T.atoms.length).trans ((Nat.le_add_right _ _).trans T.sort_rooms.1)

variable {w : ℕ} {s : Bank w} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {entry : Memory w}
    {initial written : ℕ → ℕ} (base : (pub 0).val=frame)
    (keep : CubeAllocation.HostRetention a.cube frame initial written (readings entry))
    (valid : OpenSuffix.Ready (a.openInputs team frame offsets control live ports bundles b owner hdr) frame (readings entry) w)
    (place : OpenSuffix.Placement (a.openInputs team frame offsets control live ports bundles b owner hdr)
      a.cube a.before frame (readings entry))
    (opened : Returns OpenSuffix.code pub mac s entry)
    {banks : CellBanks.Layout} {scalars digits : ℕ} {source : ℕ → ℕ}
    (directory : Reports.Directory pub opened.val.2.2 a.before banks
      (a.controlRows team frame offsets control live ports) source scalars digits)
    (bankAt : banks.bankStart=a.cube.cellBank)
    (reported : Returns prepareReports pub mac opened.val.2.1 opened.val.2.2)
    (fr : FragmentDirectoryInput pub reported.val.2.2)

include base keep valid place directory bankAt in
/-- On every actual open and scalar-report return, the three sparse input scans
use exactly the earlier charged public chooser counts, including holes in the
cable table and only populated delivery rows. The report matrix can be arbitrary. -/
theorem Layout.retained_fragment_counts :
    fr.layout.host.count=(LabelIndex.layout frame initial).cableCount ∧
      fr.layout.count=(LabelIndex.layout frame initial).deliveryCount ∧
      fr.layout.cells=(LabelIndex.layout frame initial).cells := by
  have atFrame : OpenSuffix.Ready (H) (pub 0).val (readings entry) w := by
    simpa only [base] using valid
  have read : readings opened.val.2.2=(H).image (pub 0).val (readings entry) :=
    ((OpenSuffix.run (H) atFrame).sound opened.property).2
  have image : readings opened.val.2.2=(H).image frame (readings entry) :=
    read.trans (congrArg (fun z => (H).image z (readings entry)) base)
  have preserves (j : ℕ) (old : j<112) (h13 : j ≠ 13) (h46 : j ≠ 46) (h90 : j ≠ 90) :
      readings reported.val.2.2 (frame+j)=initial (frame+j) := by
    have rb := keep.primary
    have low : frame+j<a.cube.cellBank := (show frame+j < a.cube.header.header by omega).trans_le (host_order a.cube).1
    exact (directory.low reported _ (bankAt.symm ▸ low)).trans ((congrFun image _).trans
      ((a.open_image_low owner hdr place _ low (by omega)).trans (keep.lower _ (by omega) (by omega) (by omega))))
  rw [fr.loaded]
  change readings reported.val.2.2 ((pub 0).val+7)=initial (frame+7) ∧
    readings reported.val.2.2 ((pub 0).val+9)=initial (frame+9) ∧
    readings reported.val.2.2 ((pub 0).val+11)=initial (frame+11)
  rw [base]
  exact ⟨preserves 7 (by decide) (by decide) (by decide) (by decide),
    preserves 9 (by decide) (by decide) (by decide) (by decide),
    preserves 11 (by decide) (by decide) (by decide) (by decide)⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
