import OAI.Computability.BorderVNP.DiagonalFundedReportAddresses
import OAI.Computability.BorderVNP.PackedNativeDemandCableCast

/-! # The same funded report on the original demand row indices -/

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
open TeamContraction BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows Scatter.Assignment FiniteEvaluator
open CompactMachine CellMacro.Generator

set_option quotPrecheck false
local notation3 (prettyPrint := false) "visit(" a "," U "," p ")" => PinStart.visits (a : SignedTaskArena.Layout).id U p
local notation3 (prettyPrint := false) "memory(" a "," U "," p ")" => (visit(a,U,p)).reports.val.2.2
local notation3 (prettyPrint := false) "fragment(" a "," U "," u "," p ")" =>
  FragmentRows.Layout.fromFrame (((U) (u)).pub 0).val (readings memory(a,U,p))

open Packing.RoutingOutputs

private theorem rowFibre_eq {C : ℕ} {before after : List Packing.Directory.Row}
    (same : before=after) {src : Fin before.length → Fin C} {dst : Fin after.length → Fin C}
    (sameReceiver : HEq src dst)
    (Family : (rows : List Packing.Directory.Row) → (Fin rows.length → Fin C) → Type*) :
    Family before src=Family after dst := by
  subst after
  obtain rfl := eq_of_heq sameReceiver
  rfl

/-- Removing the cable-count cast in the original seven-word demand table
reindexes its receiver and width together. The funded report, its native
source and saved placement all come from the same physical input. -/
noncomputable def EmittedReport.atOriginalDemandRows (a : SignedTaskArena.Layout) {dim edgeCount physicalCount portCount : ℕ}
    {Port : Type} [Fintype Port] {width : Port → ℕ} (network : Network dim Port width)
    (cell : network.Site → Fin a.cube.cells) (edge : network.Edge ↪ Fin edgeCount)
    (bound : edgeCount=physicalCount) (port : Port ↪ Fin portCount) (dir : Packing.Directory.Layout)
    (original : Fin dir.entries ↪ network.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ Port) (gap : ℕ)
    {teams n w : ℕ} {U : Fin (teams+1) → PinStart SparseExterior.driver n w} {u : Fin (teams+1)}
    {p : (U u).Prefix a.id} {E I P : Type} [Fintype P] {wp wd B J offsets ctl start ports : ℕ}
    {fit : (fragment(a,U,u,p)).Fits w (readings memory(a,U,p))}
    {cells : a.fragments.cells=(fragment(a,U,u,p)).cells}
    {emission : SparseEmission a (fragment(a,U,u,p)) (memory(a,U,p)) fit cells}
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
     {home : Fin J → Fin a.cube.cells}
    {layout : ReportLayout} {payload : Fin J → ReportBundle} {Seed : Prop} {seed : Seed}
    {native : PinStart.SparseSource a.id U p} {owner : ℕ → ℕ} {Index : Type*} {index : Index → ℕ}
    {want : Index → CellInput} {tags rows : ℕ} {directory : SiteWords.Directory (Fin tags) (Fin dir.entries) (rows+1)}
    {destination : dir.DestinationBounds} :
  let padded := edge.trans (finCongr bound).toEmbedding
  let reportAt (rs : List Packing.Directory.Row) (receiver : Fin rs.length → Fin a.cube.cells) :=
    {d : EmittedReport a U u p dir offsets ctl start ports E I P (Fin rs.length) wp wd B J //
      d.FundedFacts emission decl label receiver (fun i => rs[i.val].width) home layout payload seed
        native owner index want directory}
  let originalReceiver := NativeDemands.receiver network cell edge port dir original live gap destination
  let paddedReceiver := NativeDemands.receiver network cell padded port dir original live gap destination
  reportAt (NativeDemands.rows network cell padded port dir original live gap) paddedReceiver →
    reportAt (NativeDemands.rows network cell edge port dir original live gap) originalReceiver := by
  intro padded reportAt originalReceiver paddedReceiver source
  have same := NativeDemands.rows_cast_cables network cell edge bound port dir original live gap
  have receivers : HEq paddedReceiver originalReceiver := by subst physicalCount; rfl
  exact cast (rowFibre_eq same receivers reportAt) source

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
