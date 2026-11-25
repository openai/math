import OAI.Computability.BorderVNP.DiagonalSignedFrozenReportRows

/-! # A single local opened report and the original source state it represents -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator Evaluator Evaluator.SignedPrep
open Packing Packing.BottomReports Packing.RoutingOutputs DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory
open scoped Classical

variable {R J : ℕ} (t : Layout) (u : Fin (R+1)) (frame origin ports : ℕ)
    (home : Fin J → Fin t.cube.cells) (header : Fin J → BundleHeader)
    (body factors : Fin J → List CellSparse.Factor) (who supply wire : ℕ → ℕ) (w : ℕ)
local notation "table" => bases origin t.cube.cables t.cube.cells J
local notation "ctl" => controlsBase origin t.cube.cables t.cube.cells J ports
local notation "rep" => reportLayout t.before t.after frame ctl t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "directory" => t.bundleLayout frame ctl J
local notation "rows" => t.controlRows u.val frame (Bases.ends table) ctl (Bases.livePairs table) ports
local notation3 (prettyPrint := false) "packet" bits => fun j : Fin J => physicalBundle (header j) (body j) (factors j) (bits j)

/-- The single team's native state from writer entry through its directory
opening. The owner and width fields identify its actual published columns. -/
structure SingleOpenedReport where
  /-- Depth of the padded original bundle directory. -/
  bits : ℕ
  /-- Memory used to decode the receiving owner of each physical cell. -/
  input : ℕ → ℕ
  /-- Memory after publishing the geometry and the two per-cell width columns. -/
  published : ℕ → ℕ
  /-- Entry-writer memory whose retained tables are available to the owning team. -/
  written : ℕ → ℕ
  /-- Memory returned by this team’s owned traversal. -/
  owned : ℕ → ℕ
  /-- Coordinate of the cube declaration recovered by this team. -/
  axis : Fin (t.cube.n+1)
  /-- Bits read at each original bundle’s local input bank. -/
  bank : Fin J → ℕ → Bool
  /-- Count digits assigned to the native rows in global cell order. -/
  counts : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool
  entry : NativeEntry t.cube frame ctl axis R input published written
  keep : CubeAllocation.HostRetention t.cube frame published written owned
  placement : OpenSuffix.Placement
    (t.openInputs u.val frame (Bases.ends table) ctl (Bases.livePairs table) ports J bits home (ReportBundle.header ∘ (packet bank)))
    t.cube t.before frame owned
  room : t.OpenRoom frame (Bases.ends table) ctl (Bases.livePairs table) ports J (2^bits) w
  selected : ∀ c : Fin t.cube.cells, (t.cube.receivingOwner frame axis R input c.val).val=who c.val
  widths : ∀ c : Fin t.cube.cells, published ((table).ends+2*t.cube.cables+c.val)=supply c.val ∧
    published ((table).livePairs+2*ports+c.val)=wire c.val

variable {t u frame origin ports home header body factors who supply wire w}
    (o : SingleOpenedReport (R:=R) (J:=J) t u frame origin ports home header body factors who supply wire w)

/-- The installed local list comes from the actual post-open bank and stable
source ordering. Its digits and sampled bundle bank are those of this team. -/
noncomputable def SingleOpenedReport.cells : List (ReportCell rep) :=
  directoryCells directory rows rep home (packet o.bank)
    (grouped directory home (packet o.bank) (OpenSuffix.hostImage frame o.owned)) o.counts

/-- Clearing report choices yields the canonical source cells at the same
owner, bank and two physical packet widths. -/
theorem SingleOpenedReport.same_source :
    SameReportCells o.cells (sourceCells rep home (packet (fun _ _ => false)) u.val who
      (fun c => t.cube.cellBank+c*t.cube.cellStride) supply wire (fun _ _ _ => false)) :=
  t.signedReport_sourceCells u o.axis home header body factors o.bank o.input o.published o.written o.owned
    o.entry o.keep o.placement o.room who supply wire o.selected o.widths o.counts

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
