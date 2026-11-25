import OAI.Computability.BorderVNP.DiagonalEmittedReportTransport
import OAI.Computability.BorderVNP.DiagonalSparsePlacementEvidence

/-! # Relabelling the addresses of an already funded original report -/

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

variable {teams n w : ℕ} {a : SignedTaskArena.Layout}
    {U : Fin (teams+1) → PinStart SparseExterior.driver n w} {u : Fin (teams+1)} {p : (U u).Prefix a.id}
    {dir : Packing.Directory.Layout} {offsets ctl live ports : ℕ} {E I P A : Type}
    [Fintype P] [Fintype A] {wp wd B J : ℕ}

/-- The original source facts in the funded report constructor. The emitted
RAM, original seed, issued call and saved placement use the same witness. -/
abbrev EmittedReport.FundedFacts (d : EmittedReport a U u p dir offsets ctl live ports E I P A wp wd B J)
    {fit : (fragment(a,U,u,p)).Fits w (readings memory(a,U,p))}
    {cells : a.fragments.cells=(fragment(a,U,u,p)).cells}
    (emission : SparseEmission a (fragment(a,U,u,p)) (memory(a,U,p)) fit cells)
    (decl : LengthDeclaration a.cube.n a.cube.header.d) (label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d)
    (recv : A → Fin a.cube.cells) (incoming : A → ℕ) (home : Fin J → Fin a.cube.cells)
    (layout : ReportLayout) (payload : Fin J → ReportBundle) {Seed : Prop} (seed : Seed)
    (native : PinStart.SparseSource a.id U p) (owner : ℕ → ℕ) {Index : Type*} (index : Index → ℕ)
    (want : Index → CellInput) {tags rows : ℕ} (directory : SiteWords.Directory (Fin tags) (Fin dir.entries) (rows+1)) :=
  d.declaration=decl ∧ d.label=label ∧ d.recv=recv ∧ d.incoming=incoming ∧
    d.emission=emission ∧ d.home=home ∧ d.layout=layout ∧ d.payload=payload ∧ HEq d.seed seed ∧
    d.launch.native=native ∧ OwnerTable (U u).pub p.2.val.2.2 ⟨u.val,a.before.limit,a.cube.cells⟩ owner ∧
    (∀ i,d.launch.native.logicalAt (index i)=want i) ∧ Nonempty (SavedSparsePlacement directory d.launch.native.logicalAt)

local notation3 (prettyPrint := false) "report(" idx ")" =>
  EmittedReport a U u p dir (idx : ℕ × ℕ × ℕ).1 idx.2.1 idx.2.2 ports E I P A wp wd B J

/-- The original report and any dependent observation of it survive equal
offset, control, and live table addresses on the same task and prefix. -/
def EmittedReport.reindexExactAddressesWith {before after : ℕ × ℕ × ℕ} (same : before=after)
    (Q : (k : ℕ × ℕ × ℕ) → report(k) → Sort*) (d : report(before)) (receipt : Q before d) :
    (moved : report(after)) ×' Q after moved := by
  subst after
  exact ⟨d,receipt⟩

/-- In particular the moved emitter and its seed, launch, patch, issued
roster and the accompanying receipt are the ones in the original return. -/
theorem EmittedReport.reindexExactAddressesWith_keeps {before after : ℕ × ℕ × ℕ} (same : before=after)
    (Q : (k : ℕ × ℕ × ℕ) → report(k) → Sort*) (d : report(before)) (receipt : Q before d) :
    let moved := d.reindexExactAddressesWith same Q receipt
    moved.1.emission=d.emission ∧ HEq moved.1.seed d.seed ∧ HEq moved.1.patch d.patch ∧
      HEq moved.1.launch d.launch ∧ HEq moved.1.issued.roster d.issued.roster ∧ HEq moved.2 receipt := by
  subst after
  exact ⟨rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

/-- Move the complete result of the funded issuer to its equal reader
addresses, with each original source read and geometric assignment intact. -/
def EmittedReport.atReportAddresses (a : SignedTaskArena.Layout) (dir : Packing.Directory.Layout)
    (before after : ℕ × ℕ × ℕ) (ports : ℕ) (same : before=after)
    {teams n w : ℕ} {U : Fin (teams+1) → PinStart SparseExterior.driver n w} {u : Fin (teams+1)}
    {p : (U u).Prefix a.id} {E I P A : Type} [Fintype P] [Fintype A] {wp wd B J : ℕ}
    {fit : (fragment(a,U,u,p)).Fits w (readings memory(a,U,p))}
    {cells : a.fragments.cells=(fragment(a,U,u,p)).cells}
    {emission : SparseEmission a (fragment(a,U,u,p)) (memory(a,U,p)) fit cells}
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {recv : A → Fin a.cube.cells} {incoming : A → ℕ} {home : Fin J → Fin a.cube.cells}
    {layout : ReportLayout} {payload : Fin J → ReportBundle} {Seed : Prop} {seed : Seed}
    {native : PinStart.SparseSource a.id U p} {owner : ℕ → ℕ} {Index : Type*} {index : Index → ℕ}
    {want : Index → CellInput} {tags rows : ℕ} {directory : SiteWords.Directory (Fin tags) (Fin dir.entries) (rows+1)}
    (source : {d : EmittedReport a U u p dir before.1 before.2.1 before.2.2 ports E I P A wp wd B J // d.FundedFacts emission decl label recv incoming home layout payload seed
      native owner index want directory}) :
    {d : EmittedReport a U u p dir after.1 after.2.1 after.2.2 ports E I P A wp wd B J // d.FundedFacts emission decl label recv incoming home layout payload seed
      native owner index want directory} := by
  subst after
  exact source

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
