import OAI.Computability.BorderVNP.DiagonalFundedReportAddresses

/-! # Coordinates, layout and payload of an original funded report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM BorderVNP.Cube Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder
open BorderVNP.Cube.Physical BorderVNP.Cube.TeamRowClock BorderVNP.Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacketGeometry CellDispatch Packing.BundleDirectory
open DiagonalTallyCellReports.ReportDirectory
open TeamContraction BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator
open CompactMachine CellMacro.Generator

set_option quotPrecheck false
local notation3 (prettyPrint := false) "visit(" a "," U "," p ")" => PinStart.visits (a : SignedTaskArena.Layout).id U p
local notation3 (prettyPrint := false) "memory(" a "," U "," p ")" => (visit(a,U,p)).reports.val.2.2
local notation3 (prettyPrint := false) "fragment(" a "," U "," u "," p ")" =>
  FragmentRows.Layout.fromFrame (((U) (u)).pub 0).val (readings memory(a,U,p))

variable {teams n w : ℕ} {a : SignedTaskArena.Layout}
    {U : Fin (teams + 1) → PinStart SparseExterior.driver n w} {u : Fin (teams + 1)} {p : (U u).Prefix a.id}
    {dir : Packing.Directory.Layout} {offsets ctl live ports : ℕ} {E I P A : Type}
    [Fintype P] [Fintype A] {wp wd B J : ℕ}

local notation "report" => EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J

/-- The original funding receipt supplies the report coordinates, its layout in the chart,
and the saved payload used to bound its marks. -/
theorem EmittedReport.payStoredOriginalFields
    (decl : LengthDeclaration a.cube.n a.cube.header.d)
    (label : Fin a.cube.cells → Label (a.cube.n + 1) a.cube.header.d) (recv : A → Fin a.cube.cells)
    (incoming : A → ℕ) (home : Fin J → Fin a.cube.cells) (layout chart : ReportLayout) (payload : Fin J → ReportBundle)
    (coordinates marks : report → Prop)
    (paysCoordinates : ∀ d : report, d.declaration = decl → d.label = label →
      d.recv = recv → d.incoming = incoming → coordinates d)
    (paysMarks : ∀ d : report, d.payload = payload → marks d)
    (atChart : layout = chart)
    {fit : (fragment(a,U,u,p)).Fits w (readings memory(a,U,p))}
    {cells : a.fragments.cells = (fragment(a,U,u,p)).cells}
    (emission : SparseEmission a (fragment(a,U,u,p)) (memory(a,U,p)) fit cells)
    {Seed : Prop} (seed : Seed)
    (native : PinStart.SparseSource a.id U p) (owner : ℕ → ℕ) {Index : Type*} (index : Index → ℕ)
    (want : Index → CellInput) {tags rows : ℕ} (directory : SiteWords.Directory (Fin tags) (Fin dir.entries) (rows + 1))
    (original : {d : report // d.FundedFacts emission decl label recv incoming home layout payload
      seed native owner index want directory})
    : coordinates original.val ∧ original.val.layout = chart ∧ marks original.val := by
  obtain ⟨hDecl, hLabel, hRecv, hIncoming, _, _, hLayout, hPayload, _⟩ := original.property
  exact ⟨paysCoordinates original.val hDecl hLabel hRecv hIncoming,
    hLayout.trans atChart, paysMarks original.val hPayload⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
