import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits
import OAI.Computability.BorderVNP.RoutingISAScheduleClockControls
import OAI.Computability.BorderVNP.RoutingISAScheduleClockReports
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.CellSparseExteriorProgramCharge

/-! # Actual sparse report sources and the native cell clock

The report emitter reads the ordered owned cells and the three argument writers
publish their compressed tasks in the private directory. Charging those two
visits together counts each scheduled delivery and original power slot in the
same cell order as the native writers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical Cube.TeamRowClock Cube.TeamRowSources
open Crossing Packing.CellAddresses Packing.Directory DiagonalTallyCellReports
open Diagonal.ExternalSew.Fragments CellPacket CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry BorderVNP.FiniteEvaluator.OpenSuffix

private theorem originalInputs {w description : ℕ} {l : ReportLayout} {pub : Arg → Word w} {m}
    {cs : List (ReportCell l)} {q : ReportCursor} (seed : PreparedReportInput pub m cs q description) :
    cellInputs w description cs q l.headers (readings m) := by
  let original : ReportAssignments cs := ⟨cs,rfl⟩
  let tape := (reportAssignmentEquiv cs).symm original
  have same : cellsOfTape cs tape=cs := congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply original)
  rw [←same]
  exact seed.inputs _

section Cells

variable {Site E I A P : Type} [Fintype A] [Fintype P] {w : ℕ}
    {a : CubeArena.Layout} {D : LengthDeclaration a.n a.header.d} {label : Fin a.cells → Label (a.n+1) a.header.d}
    {recv : A → Fin a.cells} {incoming : A → ℕ} {pub : Arg → Word w}

set_option quotPrecheck false

/-- Read a cell's owner word at its selected product label. -/
def scheduledCellOwner (a : CubeArena.Layout) (D : LengthDeclaration a.n a.header.d)
    (label : Fin a.cells → Label (a.n+1) a.header.d) (assigned : ℕ → ℕ) (c : Fin a.cells) :=
  assigned (a.ownerBase+(label c D.1).val)

/-- Physical source data for the sparse writer and report emitter on a single
native path. The exterior spans refer to the real fragment emitter's stream,
and the ordinal in the sparse and typed task rows is the builder's global cell. -/
structure SparseReportSources (Site E I P : Type) [Fintype P] {A : Type}
    (a : CubeArena.Layout) (D : LengthDeclaration a.n a.header.d) (label : Fin a.cells → Label (a.n+1) a.header.d)
    (recv : A → Fin a.cells) (incoming : A → ℕ) (assigned : ℕ → ℕ) (team description p d R H B : ℕ)
    {pub : Arg → Word w} {m : Memory w} (src : SparseCallInput pub m)
    (f : FragmentRows.Layout) (bank : ℕ → ℕ) (l : CellControlRows.Layout) (mem : ℕ → ℕ) where
  /-- Dimension of the sewn network. -/
  z : ℕ
  /-- Number of Boolean lanes in each sewn exterior block. -/
  bits : P → ℕ
  /-- Sewn network for the sampled public history. -/
  network : Network z P bits
  /-- Receiving cell for every attained site. -/
  host : network.Site → Fin a.cells
  /-- Capacity of the numbered sewn edge directory. -/
  ne : ℕ
  /-- Capacity of the exterior port directory. -/
  np : ℕ
  /-- Number of crossing cables in the attained network. -/
  nc : ℕ
  /-- Sewn edge ordinal used by the fragment emitter. -/
  edgeID : network.Edge ↪ Fin ne
  /-- Physical port ordinal used by the fragment emitter. -/
  portID : P ↪ Fin np
  /-- The selected order of crossing cables. -/
  order : network.CrossingEdge host ≃ Fin nc
  cables : CableRows network host edgeID portID f.host bank
  /-- Physical cell and width of each transmitted directory row. -/
  installed : RowLocations ((List.range f.count).map (f.row bank)) (Fin.val : Fin a.cells → ℕ) recv incoming
  capacity : ∀ pair, load (cablePair order (crossSrc network host) (crossDst network host) label)
    (crossWidth network host ∘ order.symm) pair ≤ a.header.blocks*(a.h*a.b)
  /-- Sparse call task indexed by global cell. -/
  cells : ℕ → SparseExterior.Owned
  /-- Original opaque sources and public geometry of each cell. -/
  places : ℕ → Placed Site
  /-- Position of the geometry suffix in the task packet. -/
  geometry : ℕ → ℕ
  /-- Native source-weight bindings appended to the directory. -/
  extra : ℕ → List Record
  cellCount : l.cells=a.cells
  teamID : l.team=team
  count : src.count=l.before mem l.cells
  sparseCount : src.layout.count=l.before mem l.cells
  /-- Supplied bit at each addressed receiving slot. -/
  data : ℕ → ℕ → Bool
  spans : ∀ c : Fin a.cells, scheduledCellOwner a D label assigned c=team → (cells c.val).field.spans=Diagonal.ExternalSew.Fragments.spans (f.stream bank) data c.val
  ordered : ∀ c : Fin a.cells, scheduledCellOwner a D label assigned c=team → SparseExterior.Ordered (cells c.val).field.width 0 (cells c.val).field.spans
  width : ∀ c : Fin a.cells, scheduledCellOwner a D label assigned c=team → (cells c.val).field.width<2^w
  /-- Size of the static site rectangle. -/
  sites : ℕ
  /-- Live public geometry template for the attained history. -/
  template : LiveWords.Template E I Site sites (a.cells+1)
  /-- Cell field of each native site row. -/
  site : Fin sites → Fin (a.cells+1)
  /-- Value of a public expression in the current geometry branch. -/
  arg : E → ℕ
  /-- Values of the sparse fields in each static site row. -/
  fields : Fin sites → I → ℕ
  shape : TypedBatch.SourceFootprint (fun c => places c.val) (template.directory site arg fields)
  publicRoom : (a.cells+1)+template.atoms.length+(a.cells+1) ≤ 2^p
  descriptorRoom : (a.cells+1)+(Schema.coords template.chunkLabels.length).length+(a.cells+1) ≤ 2^d
  /-- Native width and cell-header layout of the report scanner. -/
  layout : ReportLayout
  /-- Proposed counts and individual uses indexed by global cell. -/
  reports : Fin a.cells → ReportCell layout
  /-- Local cursor for constructing the source-weight bindings. -/
  cursor : Fin a.cells → LocalReportCursor
  /-- Address of the first bundle header in each cell. -/
  bundleBase : Fin a.cells → ℕ
  /-- Actual RAM words used to authenticate original bundle records. -/
  memory : Fin a.cells → ℕ → ℕ
  reportCount : ∀ c : Fin a.cells, (places c.val).reports.length=layout.gadgets
  digits : ∀ c : Fin a.cells, ∀ v ∈ (places c.val).reports, v.length=layout.countWidth
  tails : ∀ c : Fin a.cells, scheduledCellOwner a D label assigned c=team → (cells c.val).field.tail.length=(reports c).tailWidth
  /-- Disjoint delivered bit positions for the original opaque boxes. -/
  hidden : BitDelivery (fun j : (c : Fin a.cells) × Fin ((places c.val).boxes.filterMap Sum.getRight?).length => j.1)
    (fun _ => description) recv incoming
  /-- Disjoint delivered bit positions for the original bundle descriptions. -/
  bundles : BitDelivery (fun j : (c : Fin a.cells) × Fin (reports c).bundles.length => j.1)
    (fun _ => description) recv incoming
  frameCount : (CellDispatch.Frame.ofMemory pub src.compressed).count=a.cells
  body : ∀ c < l.cells, l.owner mem c=l.team → ∀ j, (places c).headerWidth+(boxBody ((places c).factors j)).length ≤ description
  owners : ∀ c : Fin a.cells, l.owner mem c.val=scheduledCellOwner a D label assigned c
  binding : ∀ c, scheduledCellOwner a D label assigned c=team → extra c.val=bindingRows (reports c).bundles (cursor c)
  bundleInput : ∀ c, scheduledCellOwner a D label assigned c=team → bundleInputs w layout description (reports c).bundles (cursor c) (bundleBase c) (memory c)
  /-- Original team, parameter and binary place of every issued use position. -/
  original : ((c : {c : Fin a.cells // scheduledCellOwner a D label assigned c=team}) × UsePositions (reports c.val).bundles) ↪
    Diagonal.CellEntries.PowerSlot (Fin R) (Fin H) B
  sparseRows : src.owned=fun i => cells (TypedTaskBuilder.globalCell l.toLayout mem i)
  typedRows : src.tasks=fun i => (SparseExterior.supplementalRow l mem src.layout cells places geometry extra i).typed

variable {assigned orig : ℕ → ℕ} {r description p d R H B : ℕ} {team : Fin (r+1)}
    {m : Memory w} {src : SparseCallInput pub m} {f : FragmentRows.Layout} {bank : ℕ → ℕ}
    {l : CellControlRows.Layout} {mem : ℕ → ℕ}
    (S : SparseReportSources Site E I P a D label recv incoming assigned team.val description p d R H B src f bank l mem)

local notation "weights" => LocalRow.weightLayout a (pub 0).val D.1.val
local notation "teams" => LocalRow.teamLayout a r

omit [Fintype A] in
/-- Charge each visited real cell to the full public sort and descriptor sort,
including the sentinel position allocated in both physical tables. -/
theorem SparseReportSources.geometryCounts (owner : Fin a.cells → ℕ) (u : ℕ) :
    assignedSum owner u (fun c => ((S.places c.val).parts.flatMap Part.publicBuffer).length) ≤ 2^p ∧
      assignedSum owner u (fun c => (S.places c.val).boxes.length+6) ≤ 2^d :=
  TypedBatch.real_geometry_counts_of_footprint S.template S.site S.arg S.fields S.places S.shape S.publicRoom S.descriptorRoom owner u

include S in
omit [Fintype A] in
/-- The physical public sort reserves both boundaries of each allocated cell. -/
theorem SparseReportSources.cellFit : a.cells≤2^p := by
  have fit := S.publicRoom
  omega

/-- The report rows in the same compact order as the sparse and typed arguments. -/
noncomputable def SparseReportSources.reportRows :=
  List.ofFn fun i => S.reports (SparseExterior.programOrder l mem (scheduledCellOwner a D label assigned) team.val S.cellCount S.teamID S.owners i).val

/-- Charge the native compressed initializer, its probes and the original
report loops from the shared schedule, public geometry and delivered site records. -/
theorem SparseReportSources.charge {X : ℕ} (schedule : GroupWeights.ScheduleResult weights teams orig assigned)
    (image : GroupWeights.PhysicalImage weights orig a.header.blocks a.b a.K a.h D label recv incoming)
    (hw : 0<w) (positive : 1 ≤ description) (pass : (TeamBudget.Layout.mk (r+1) X a.teamTotals).Passes assigned)
    {reportMem : Memory w} {q : ReportCursor} (seed : PreparedReportInput pub reportMem S.reportRows q description)
    (final : Memory w) :
    sparseCallTicks src.layout src.owned src.tasks (CellDispatch.Frame.ofMemory pub src.compressed) final src.count+
      (prepareSetup.slots+cellTicks S.reportRows q+(writeFrame 32 60 61 35).slots) ≤ cellWork w (2^p+2^d) (R*(H*B)) X := by
  have stored (i : ℕ) (hi : i<l.before mem l.cells) :
      (SparseExterior.supplementalRow l mem src.layout S.cells S.places S.geometry S.extra i).typed.cell.Stored src.compressed := by
    have st := (src.typed.stored i (S.count ▸ hi)).2
    rwa [S.typedRows] at st
  have localLoad := ((TeamBudget.Layout.mk (r+1) X a.teamTotals).passes_iff_rational assigned).mp pass |>.1 team.val team.isLt
  rw [S.sparseRows,S.typedRows,S.count]
  exact SparseExterior.programCharge_le schedule image team X w description hw positive localLoad
    S.network S.host S.edgeID S.portID S.order f.host bank (fun c => bank (f.supplied+c)) ((List.range f.count).map (f.row bank))
    S.data S.cables S.installed S.capacity l mem src.layout S.cells S.places S.geometry S.extra S.cellCount S.teamID S.sparseCount
    S.spans S.ordered S.width S.template S.site S.arg S.fields S.shape p d S.publicRoom S.descriptorRoom S.layout S.reports
    S.cursor S.bundleBase S.memory S.reportCount S.digits S.tails S.hidden S.bundles pub src.compressed final S.frameCount stored
    S.body R H B q S.layout.headers (readings reportMem) S.owners S.binding S.bundleInput S.original (originalInputs seed)

end Cells

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
