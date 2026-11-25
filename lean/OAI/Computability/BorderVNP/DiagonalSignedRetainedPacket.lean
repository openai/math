import OAI.Computability.BorderVNP.DiagonalSignedReportPacketMemory
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.CubeRouteProfileControls

/-! # Original packet readback across the entire signed routing and report prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Packing Packing.RoutingOutputs PackedHistoryCircuit FiniteEvaluator DiagonalTallyAllocation
open DiagonalTallyCellReports CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry.History.Native

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    {origin cables cells entries desc gap next rect team offsets live ports bundles b : ℕ}
    {a : SignedTaskArena.Layout} {id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ}
    {before placed : Memory w} (rows : List Directory.Row) (V : SignedPrep.Visits id pub mac s m)
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → Packing.BottomReports.BundleHeader)
local notation "frame₀" => readings pub 0
local notation "ctl₀" => controlsBase origin cables cells entries rect
local notation "H" => a.openInputs team frame₀ offsets ctl₀ live ports bundles b owner header
local notation "initial" => readings (Directory.ISA.publish placed frame₀ next rows)
variable (slots : (privateLayout (readings pub 0) origin cables cells entries desc gap).Image
      (readings before) entries (readings placed))
    (lower : readings pub 0+112≤next) (space : next+7*rows.length≤origin)
    {written : ℕ → ℕ} (retained : CubeAllocation.HostRetention a.cube (readings pub 0)
      (readings (Directory.ISA.publish placed (readings pub 0) next rows)) written (readings V.owned.val.2.2))
    (position : OpenSuffix.Placement (a.openInputs team (readings pub 0) offsets (controlsBase origin cables cells entries rect) live ports bundles b owner header) a.cube a.before (readings pub 0) (readings V.owned.val.2.2))
    (ready : OpenSuffix.Ready (a.openInputs team (readings pub 0) offsets (controlsBase origin cables cells entries rect) live ports bundles b owner header) (readings pub 0) (readings V.owned.val.2.2) w)

include slots lower space retained position ready in
/-- Every word from the signed public packet survives the private-slot writer,
seven-word demand compaction, checked schedule/ownership and all four control
passes. The address is compared to the original geometry result, before all
route and private assignments. -/
theorem signed_geometry_word_on_visits (z : ℕ) (lo : ctl₀+37≤z) (hi : z<a.cube.header.header) :
    V.controls.val.2.2 z=before z := by
  have start : origin ≤ ctl₀ := by dsimp only [controlsBase,bases]; omega
  have control : ctl₀+(z-ctl₀)=z := by omega
  have raw := directoryPublished_control (live:=rect) rows slots lower space (z-ctl₀)
  change Directory.ISA.publish placed frame₀ next rows (ctl₀+(z-ctl₀)) = before (ctl₀+(z-ctl₀)) at raw
  rw [control] at raw
  have h := congrFun ((OpenSuffix.run (H) ready).sound V.controls.property).2 z
  change readings V.controls.val.2.2 z=(H).image frame₀ (readings V.owned.val.2.2) z at h
  have frame : frame₀+112≤z := by omega
  have openWord := a.open_image_low owner header position z (hi.trans_le a.open_table_order.1) (by omega)
  apply Fin.ext
  exact (h.trans openWord).trans ((retained.lower z hi (by omega) (by omega)).trans (congrArg Fin.val raw))

include slots lower space retained position ready in
/-- At the actual report return, each original descriptor, public geometry
block and reserved triple still equals the data emitted by the geometry DAG.
The reported counts and use digits can be arbitrary. -/
theorem signed_report_packet_on_visits {O : Type} {P : Placed O} {g last description : ℕ}
    {l : ReportLayout} {reports : List (ReportCell l)} {q : ReportCursor} {banks : CellBanks.Layout}
    (source : CellMemory P g last (readings before))
    (allocated : ReportAllocation a.before a.after banks l reports q)
    (seed : PreparedReportInput pub V.controls.val.2.2 reports q description)
    (bank : a.cube.header.header ≤ banks.bankStart)
    (descriptors : ctl₀+37≤P.descriptorBase ∧ last≤a.cube.header.header)
    (publicRange : ctl₀+37≤P.publicBase ∧ P.publicBase+((Supplement.prefixParts P).flatMap Part.publicBuffer).length≤a.cube.header.header)
    (geom : ctl₀+37≤g ∧ g+(fieldList record P.rows++fieldList vector P.reports).length≤a.cube.header.header) :
    CellMemory P g last (readings V.reports.val.2.2) := by
  have sourceAt : CellMemory P g last (readings V.controls.val.2.2) :=
    source.at_checkpoint descriptors publicRange geom (fun z lo hi =>
      congrArg Fin.val (signed_geometry_word_on_visits rows V owner header slots lower space retained position ready z lo hi))
  have start : origin ≤ ctl₀ := by dsimp only [controlsBase,bases]; omega
  have same : frame₀=l.frame := seed.framePointer
  exact sourceAt.report_return allocated seed V.reports ⟨by rw [←same]; omega,bank⟩ descriptors publicRange geom

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
