import OAI.Computability.BorderVNP.DiagonalSupportedVisitFinish
import OAI.Computability.BorderVNP.DiagonalSupportedPostSources
import OAI.Computability.BorderVNP.DiagonalSupportedFinishSizes
import OAI.Computability.BorderVNP.DiagonalUniformPostReceipt
import OAI.Computability.BorderVNP.DiagonalSelectedPostWindows

/-! # Source-sized finish of the actual signed native visits -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator Evaluator DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyRAM DiagonalTallyMaterialize BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Physical
open BorderVNP.Cube.Padding.Banks TeamContraction.ProcessorSlots TeamContraction.JointHeader
open TeamContraction.JointHeader.PositiveFields Evaluator.ScheduleClock Crossing
open TeamScales CellPacketGeometry
open scoped Classical
open private tape_map from OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsTape
set_option quotPrecheck false

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : Layout) {R : ℕ} (teamCount : a.cube.teams=R+1) (team : Fin a.cube.teams)
    (offsets ctl live ports : ℕ) (owner : Fin a.cube.header.d → ℕ) (demand : ℕ)
    (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)
    (V : SignedPrep.Visits a.id pub mac s m)
    {Site E I Operand P : Type} [Fintype P] [Fintype Operand] {description p d B : ℕ}
    {decl : LengthDeclaration a.cube.n a.cube.header.d} {label : Fin a.cube.cells → Label (a.cube.n+1) a.cube.header.d}
    {recv : Operand → Fin a.cube.cells} {incoming : Operand → ℕ} {assigned : ℕ → ℕ}
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
local notation3 (prettyPrint := false) "X" => gadgetLookup a pub owner team.val demand A
local notation "head" => (pub 0).val
local notation3 (prettyPrint := false) "ctrl" => a.controlRows team.val head offsets ctl live ports
variable (src : SparseCallInput pub ((argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments).2.1.val.2.2)
    {f : FragmentRows.Layout} {routed : ℕ → ℕ}
    (S : SparseReportSources Site E I P a.cube decl label recv incoming assigned team.val description p d
      a.cube.teams a.p.parameters B src f routed (a.controlRows team.val (pub 0).val offsets ctl live ports)
      (readings ((argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments).1.val.2.2))
local notation3 (prettyPrint := false) "rs" => S.reportRows (team := Fin.cast teamCount team)
local notation3 (prettyPrint := false) "L" => S.layout
local notation3 (prettyPrint := false) "weights" => LocalRow.weightLayout a.cube head A.axis.val
local notation3 (prettyPrint := false) "teams" => LocalRow.teamLayout a.cube R

set_option maxHeartbeats 2100000 in
/-- At any supported return the physical ID scan and both actual sparse report
loops fit their selected phase charges. All counts are derived from the
same concrete task source and the original checked group-owner table. -/
theorem physicalPost_on_scheduled_visits {q : ReportCursor} {banks : CellBanks.Layout} {initialMem : ℕ → ℕ}
    (scheduled : GroupWeights.ScheduleResult weights teams initialMem assigned)
    (image : GroupWeights.PhysicalImage weights initialMem a.cube.header.blocks a.cube.b a.cube.K a.cube.h
      decl label recv incoming) (stored : ∀ i : Fin a.cube.header.d, owner i = assigned ((teams).owners+i.val))
    (X₀ : ℕ) (positive : 0<a.cube.h*a.cube.b) (alphabet : 0<a.cube.header.d)
    (pass : (TeamBudget.Layout.mk (R+1) X₀ (teams).totals).Passes assigned)
    (seed : PreparedReportInput pub V.controls.val.2.2 rs q description)
    (alloc : ReportAllocation a.before a.after banks (L) rs q)
    (deck : CubePacket.WordPrepared X a.id pub V.owned.val.2.2)
    (H : OpenSuffix.Inputs) (openPlace : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (openReady : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (packet : A.packetBase=a.cube.header.packetBase)
    (start : banks.bankStart=a.cube.cellBank) (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (zero : (L).zeroAddr=a.cube.stop) (wpos : 0<w) (dim : (L).parameters+(L).gadgets≤2^w) (width : (L).countWidth≤w)
    (source : ∀ c∈rs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (sortedLo : head+112≤(ctrl).sorted) (sortedHi : (ctrl).sorted+(ctrl).padded≤a.cube.header.packetBase)
    (ctlLo : head+112≤ctl) (ctlHi : ctl+37≤a.cube.header.packetBase)
    {u v k : ℕ} (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (pointer : readings V.reports.val.2.2 (head+92)=ctl)
    (controls : ∀ j : Fin 37, readings V.reports.val.2.2 (ctl+j.val)=a.controls j.val)
    (nc : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (nr : readings V.reports.val.2.2 (head+9)≤a.cube.maxRows) (cc : readings V.reports.val.2.2 (head+11)=a.cube.cells)
    (space : a.endAddress w u v k<2^w)
    (production : ProducedRoster a ctrl (readings (parts).1.val.2.2) S.places S.geometry S.extra src)
    {reserve axes groups hdrCap subt : ℕ} (startup : StartupArena)
    (fields : PositiveFields reserve axes groups hdrCap a.cube.teams a.dim subt)
    (initial : HeaderSeed a fields pub (rawAddress startup reserve axes groups hdrCap) team.val V.arguments.val.2.2)
    (headEq : head=startup.frame) (layout : (L).parameters=a.p.parameters ∧ (L).gadgets=a.p.report.gadgets)
    (vertices : (X).frame.count ≤ a.p.report.vertices)
    (digits : argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ≤ a.p.report.cubeWidth)
    (ids : ∀ i,a.id (((X).visits i).entry demand)<(L).gadgets)
    (header : startup.header=PositiveFields.width reserve axes groups hdrCap a.cube.teams a.dim subt)
    (position : startup.next≤a.cube.header.header) (teamFit : a.cube.teams<2^w) (subtWidth : subt≤w)
    (call : Returns callOwnedCells pub mac V.arguments.val.2.1 V.arguments.val.2.2)
    (z : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2)
    {batch length logPower readerTicks : ℕ} {α ξ : ℝ}
    (windows : a.FinishWindows batch w p d B X₀
      ⌈publicWork (a.cube.n+1) α batch length a.cube.teams⌉₊
      ⌈localWork (a.cube.n+1) logPower α ξ batch length a.cube.teams⌉₊ readerTicks) :
    let P₀ := ⌈publicWork (a.cube.n+1) α batch length a.cube.teams⌉₊
    let L₀ := ⌈localWork (a.cube.n+1) logPower α ξ batch length a.cube.teams⌉₊
    let W := argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    let F := cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s W
    let H₀ := TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s
    Nonempty (PinStart.PhysicalPost (d:=a.dim) (width:=subt) team a P₀ L₀ F H₀
      pub mac call.val.2.1 call.val.2.2 z) := by
  intro P₀ L₀ W F H₀
  let units := (a.cube.header.d^(a.cube.n+1))^2+X₀+1
  let powers := a.cube.teams*(a.p.parameters*B)
  obtain ⟨_,_,_,_,clock⟩ := finish_on_supported_visits a team offsets ctl live ports owner demand A V
    seed alloc deck H openPlace openReady packet start count stride zero wpos dim width source sortedLo sortedHi ctlLo ctlHi
    place fit pointer controls nc nr cc space S.places S.geometry S.extra ⟨src,production⟩ startup fields initial
    headEq layout vertices digits ids header position teamFit subtWidth call z
  have measured := S.finish_sizes (team:=Fin.cast teamCount team)
  let bits := (reportReturnEquiv seed mac V.controls.val.2.1).symm V.reports
  let tape := fun i => if h : i<(reportBits rs).length then bits ⟨i,h⟩ else false
  have same : teamWeighted (cellsOfTape rs bits)=teamWeighted rs := by
    change ((tapeCells tape 0 rs).map _).sum=_
    rw [tape_map tape (fun c => weightedCopies c.bundles) (fun c j => by simp [ReportCell.withTape,weightedCopies]) rs 0]
    rfl
  have nvisit := gadgetLookup_visited_le a pub owner R (Fin.cast teamCount team) demand A initialMem assigned
    scheduled image stored X₀ positive alphabet pass
  exact (clock (2^p+2^d) powers units (by simpa only [cellsOfTape,tapeCells_length] using measured.1)
    (same.le.trans measured.2) (Nat.succ_pos _)
    (nvisit.trans (Nat.mul_le_mul_left _ (Nat.le_succ _)))).2 P₀ L₀ windows.sorts windows.powers windows.units

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
