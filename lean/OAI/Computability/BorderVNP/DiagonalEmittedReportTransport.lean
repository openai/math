import OAI.Computability.BorderVNP.DiagonalIssuedArgumentWindow
import OAI.Computability.BorderVNP.DiagonalNativeInputAt

/-! # Relabelling the report issued on one actual argument prefix -/

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

variable {teams n w : ℕ} (a : SignedTaskArena.Layout)
    (U : Fin (teams+1) → PinStart SparseExterior.driver n w) (u : Fin (teams+1)) (p : (U u).Prefix a.id)
    (dir : Packing.Directory.Layout) (offsets ctl live ports : ℕ) (E I P A : Type)
    [Fintype P] [Fintype A] (wp wd B J : ℕ)

set_option quotPrecheck false
local notation3 (prettyPrint := false) "vis" => PinStart.visits a.id U p
local notation3 (prettyPrint := false) "orig" => (vis).reports.val.2.2
local notation3 (prettyPrint := false) "fr" => FragmentRows.Layout.fromFrame ((U u).pub 0).val (readings orig)
local notation3 (prettyPrint := false) "scan" => a.controlRows u.val ((U u).pub 0).val offsets ctl live ports
local notation3 (prettyPrint := false) "stages" =>
  (argumentVisitsEquiv (U u).pub (CompactMachine.install SparseExterior.driver n (U u).routines)
    (vis).reports.val.2.1 orig).symm (vis).arguments

/-- The report issuer's actual emitter and its dependent operands, including the
original report seed and the roster returned at that emitter's argument cut. -/
structure EmittedReport where
  /-- The returned memory fits the fragment layout decoded from its own controls. -/
  fit : (fr).Fits w (readings orig)
  /-- The decoded layout has exactly the cells reserved by the signed arena. -/
  cells : a.fragments.cells=(fr).cells
  /-- The actual emitter and bucket program on the returned reports. -/
  emission : SparseEmission a fr orig fit cells
  /-- Physical bit function read to build the sparse cell rows. -/
  data : ℕ → ℕ → Bool
  /-- The placed cells and packet bodies installed by this emitter. -/
  patch : SparsePatch (w:=w) (Fin dir.entries) scan (readings emission.output)
  /-- Original cell inputs in the native compressed order. -/
  row : (i : Fin ((scan).toLayout.before (readings emission.output) a.cube.cells)) →
    SparseCell a fr orig data i.val
  /-- Lengths of the rows in the original public declaration. -/
  declaration : LengthDeclaration a.cube.n a.cube.header.d
  /-- The group labels of the original physical cells. -/
  label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d
  /-- Receiving cell for each physical incidence. -/
  recv : A → Fin a.cube.cells
  /-- Width of each incoming incidence. -/
  incoming : A → ℕ
  /-- Layout in which the original reports were formed. -/
  layout : ReportLayout
  /-- The receiving cell of each input bundle. -/
  home : Fin J → Fin a.cube.cells
  /-- The original bundles in source order. -/
  payload : Fin J → ReportBundle
  /-- The external bits counted at each source cell. -/
  external : ℕ → ℕ
  /-- The supplied bits counted at each source cell. -/
  supply : ℕ → ℕ
  /-- Width of the private argument at each source cell. -/
  privateWidth : ℕ → ℕ
  /-- Scalar report bits indexed by their original positions. -/
  digits : ℕ → Fin layout.gadgets → Fin layout.countWidth → Bool
  /-- The cursor used to open the original report tape. -/
  cursor : ReportCursor
  /-- The tape seed on the exact owned cell list scanned by the emitter. -/
  seed : PreparedReportInput (U u).pub (vis).controls.val.2.2
    (sourceCells layout home payload u.val ((scan).owner (readings emission.output)) external supply privateWidth digits)
    cursor dir.description
  /-- The input returned by the native sparse argument builder. -/
  launch : SparseEmission.NativeInputAt (team:=u.val) (frame:=((U u).pub 0).val) (offsets:=offsets) (ctl:=ctl)
    (live:=live) (ports:=ports) a.id U p emission patch row dir.description
  /-- The physical report assembled for that same input. -/
  issued : SparseEmission.IssuedReportData (E:=E) (I:=I) (P:=P) (wp:=wp) (wd:=wd) (copies:=a.cube.teams)
    (H:=a.p.parameters) (B:=B) a a.id U p emission dir patch row declaration label recv incoming
    layout home payload external supply privateWidth digits seed
  /-- Issuer and argument builder observed exactly the same native source. -/
  native_eq : issued.native=launch.native
  /-- The bucket registers equal the registers at the actual returned stage. -/
  bank_eq : emission.bank=(stages).1.val.2.1
  /-- The bucket RAM equals the RAM at the actual returned stage. -/
  output_eq : emission.output=(stages).1.val.2.2

variable {a U u p dir offsets ctl live ports E I P A wp wd B J}
local notation3 (prettyPrint := false) "rowAt(" task "," run ")" =>
  EmittedReport task U u run dir offsets ctl live ports E I P A wp wd B J

/-- The argument window uses the word array produced by this report's emitter. -/
abbrev EmittedReport.Window (d : rowAt(a,p)) (X budget : ℕ) :=
  PinStart.PublishedArgumentWindow a a.id U p d.declaration d.label d.recv d.incoming X dir.description
    wp wd a.cube.teams a.p.parameters B fr scan (readings d.emission.output) budget

/-- Relabel every operand together at an equal layout on the same recorded prefix. -/
def EmittedReport.reindex (d : rowAt(a,p)) {b : SignedTaskArena.Layout} (layoutEq : a=b)
    (q : (U u).Prefix b.id) (same : HEq p q) : rowAt(b,q) := by
  subst b
  obtain rfl := eq_of_heq same
  exact d

/-- Any further dependent observation on the report, including the published window
with its specified profile and assignment, travels with the same emitter. -/
def EmittedReport.reindexWith (d : rowAt(a,p))
    (Q : (b : SignedTaskArena.Layout) → (q : (U u).Prefix b.id) → rowAt(b,q) → Sort*)
    {b : SignedTaskArena.Layout} (layoutEq : a=b) (q : (U u).Prefix b.id) (same : HEq p q)
    (observed : Q a p d) : Q b q (d.reindex layoutEq q same) := by
  subst b
  obtain rfl := eq_of_heq same
  exact observed

/-- The report's original seed, launch, issued data and roster all have their
original values after relabelling. The untyped RAM outputs are literally equal. -/
theorem EmittedReport.reindex_observations (d : rowAt(a,p)) {b : SignedTaskArena.Layout} (layoutEq : a=b)
    (q : (U u).Prefix b.id) (same : HEq p q) :
    let d' := d.reindex layoutEq q same
    d'.emission.output=d.emission.output ∧ d'.emission.bank=d.emission.bank ∧
      d'.layout=d.layout ∧ d'.payload=d.payload ∧ HEq d'.seed d.seed ∧
      HEq d'.launch d.launch ∧ HEq d'.issued d.issued ∧ HEq d'.issued.roster d.issued.roster := by
  subst b
  obtain rfl := eq_of_heq same
  exact ⟨rfl,rfl,rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

section Publication

variable (dir : Packing.Directory.Layout) (origin : ℕ)
local notation3 (prettyPrint := false) "offsetAt(" c ")" =>
  (Packing.RoutingOutputs.bases origin (c : SignedTaskArena.Layout × ℕ × ℕ).2.2 c.2.1 dir.entries).ends
local notation3 (prettyPrint := false) "controlAt(" c ")" =>
  Packing.RoutingOutputs.controlsBase origin (c : SignedTaskArena.Layout × ℕ × ℕ).2.2 c.2.1 dir.entries ports
local notation3 (prettyPrint := false) "liveAt(" c ")" =>
  (Packing.RoutingOutputs.bases origin (c : SignedTaskArena.Layout × ℕ × ℕ).2.2 c.2.1 dir.entries).livePairs
local notation3 (prettyPrint := false) "publishedRow(" c "," run ")" =>
  EmittedReport (c : SignedTaskArena.Layout × ℕ × ℕ).1 U u run dir offsetAt(c) controlAt(c) liveAt(c)
    ports E I P A wp wd B J

/-- Relabel the task and the physical rectangle used for the three row
addresses together, preserving any observation on the original report. -/
def EmittedReport.reindexPublication {before after : SignedTaskArena.Layout × ℕ × ℕ}
    {source : (U u).Prefix before.1.id} (d : publishedRow(before,source))
    (Q : (c : SignedTaskArena.Layout × ℕ × ℕ) → (q : (U u).Prefix c.1.id) → publishedRow(c,q) → Sort*)
    (eq : before=after) (q : (U u).Prefix after.1.id) (same : HEq source q)
    (observed : Q before source d) : (report : publishedRow(after,q)) ×' Q after q report := by
  subst after
  obtain rfl := eq_of_heq same
  exact ⟨d,observed⟩

/-- Even when the report addresses are rewritten with the network rectangle,
the emitter, issued source, native roster and its attached witness are precisely
the ones originally returned on this prefix. -/
theorem EmittedReport.reindexPublication_preserves {before after : SignedTaskArena.Layout × ℕ × ℕ}
    {source : (U u).Prefix before.1.id} (d : publishedRow(before,source))
    (Q : (c : SignedTaskArena.Layout × ℕ × ℕ) → (q : (U u).Prefix c.1.id) → publishedRow(c,q) → Sort*)
    (eq : before=after) (q : (U u).Prefix after.1.id) (same : HEq source q)
    (observed : Q before source d) :
    let moved := d.reindexPublication dir origin Q eq q same observed
    moved.1.emission.output=d.emission.output ∧ moved.1.emission.bank=d.emission.bank ∧
      HEq moved.1.seed d.seed ∧ HEq moved.1.launch d.launch ∧ HEq moved.1.issued.roster d.issued.roster ∧
      HEq moved.2 observed := by
  subst after
  obtain rfl := eq_of_heq same
  exact ⟨rfl,rfl,HEq.rfl,HEq.rfl,HEq.rfl,HEq.rfl⟩

end Publication

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
