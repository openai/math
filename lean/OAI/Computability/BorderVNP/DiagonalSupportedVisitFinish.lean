import OAI.Computability.BorderVNP.DiagonalLocalPacketFinish
import OAI.Computability.BorderVNP.DiagonalUniformPostReceipt
import OAI.Computability.BorderVNP.DiagonalSignedPreparedOperands

/-! # Actual finish receipts and clocks after the full supported pre-call program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM FiniteEvaluator RoutingISA.Evaluator DiagonalTallyAllocation DiagonalTallyCellReports
open DiagonalTallyRAM DiagonalTallyMaterialize BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.Evaluator.ScheduleClock

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
    (a : Layout) (team : Fin a.cube.teams) (offsets ctl live ports : ℕ)
    (owner : Fin a.cube.header.d → ℕ) (demand : ℕ)
    (A : Data a.cube.n a.cube.header.d a.cube.header.blocks a.cube.b a.cube.h a.cube.K a.cube.s)
set_option quotPrecheck false
local notation "X" => gadgetLookup a pub owner team.val demand A
local notation "head" => (pub 0).val
local notation "controlRows" => a.controlRows team.val head offsets ctl live ports

/-- From the original owned packet and actually returned pin/route/report/task
instructions, construct the receipt and uniform finish charge at each subsequent
private-call return. Guesses from the report tape may be arbitrary. -/
theorem finish_on_supported_visits {l : ReportLayout} {cs : List (ReportCell l)} {q : ReportCursor}
    {description : ℕ} {banks : CellBanks.Layout} (V : SignedPrep.Visits a.id pub mac s m)
    (seed : PreparedReportInput pub V.controls.val.2.2 cs q description)
    (alloc : ReportAllocation a.before a.after banks l cs q)
    (deck : CubePacket.WordPrepared X a.id pub V.owned.val.2.2)
    (H : OpenSuffix.Inputs) (openPlace : OpenSuffix.Placement H a.cube a.before head (readings V.owned.val.2.2))
    (openReady : OpenSuffix.Ready H head (readings V.owned.val.2.2) w)
    (packet : A.packetBase=a.cube.header.packetBase)
    (start : banks.bankStart=a.cube.cellBank) (count : banks.cells=a.cube.cells) (stride : banks.stride=a.cube.cellStride)
    (zero : l.zeroAddr=a.cube.stop) (wpos : 0<w) (dim : l.parameters+l.gadgets≤2^w) (width : l.countWidth≤w)
    (source : ∀ c∈cs, ∀ b∈c.bundles, ∀ p∈b.positions, p.parameter<2^w ∧ p.place<w)
    (sortedLo : head+112≤(controlRows).sorted) (sortedHi : (controlRows).sorted+(controlRows).padded≤a.cube.header.packetBase)
    (ctlLo : head+112≤ctl) (ctlHi : ctl+37≤a.cube.header.packetBase)
    {u v k : ℕ} (place : a.SparsePlacement head ctl)
    (fit : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).Fits w (readings V.reports.val.2.2))
    (pointer : readings V.reports.val.2.2 (head+92)=ctl)
    (controls : ∀ j : Fin 37, readings V.reports.val.2.2 (ctl+j.val)=a.controls j.val)
    (nc : (FragmentRows.Layout.fromFrame head (readings V.reports.val.2.2)).host.count=a.cube.cables)
    (nr : readings V.reports.val.2.2 (head+9)≤a.cube.maxRows) (cc : readings V.reports.val.2.2 (head+11)=a.cube.cells)
    (space : a.endAddress w u v k<2^w)
    {Site : Type} (placedSide : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac V.reports.val.2.1 V.reports.val.2.2).symm V.arguments
      ∃ src : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2,
        ScheduleClock.ProducedRoster a controlRows (readings parts.1.val.2.2) placedSide geom extra src)
    {reserve axes groups hdrCap subt : ℕ} (startup : StartupArena)
    (fields : PositiveFields reserve axes groups hdrCap a.cube.teams a.dim subt)
    (initial : HeaderSeed a fields pub (rawAddress startup reserve axes groups hdrCap) team.val V.arguments.val.2.2)
    (headEq : head=startup.frame) (layout : l.parameters=a.p.parameters ∧ l.gadgets=a.p.report.gadgets)
    (vertices : (X).frame.count ≤ a.p.report.vertices)
    (digits : argumentWidth a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s ≤ a.p.report.cubeWidth)
    (ids : ∀ i,a.id (((X).visits i).entry demand)<l.gadgets)
    (header : startup.header=PositiveFields.width reserve axes groups hdrCap a.cube.teams a.dim subt)
    (position : startup.next≤a.cube.header.header) (teamFit : a.cube.teams<2^w) (subtWidth : subt≤w)
    (call : Returns callOwnedCells pub mac V.arguments.val.2.1 V.arguments.val.2.2)
    (z : Returns (finishExpansion signedOccurrences) pub mac call.val.2.1 call.val.2.2) :
    let reports := cellsOfTape cs ((reportReturnEquiv seed mac V.controls.val.2.1).symm V.reports)
    ∃ rows : Fin a.cube.teams → Fin a.dim → ℕ,
    ∃ receipt : FinishInput team rows subt pub mac call.val.2.1 call.val.2.2 fields.tallyWords,
      receipt.post=a.after ∧
      (∀ i<a.after.start, i≠head+35 → receipt.selected i=call.val.2.2 i) ∧
      ∀ pubWords powers units, reports.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pubWords →
        teamWeighted reports ≤ powers → 1 ≤ units →
        (X).frame.count ≤ TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s * units →
        traceCost z.val.1 ≤ cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s (X).frame.width*units +
          64*(pubWords+powers+TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s*units)+
          512*(a.cube.teams+1)*(a.dim+1)*(w+1) ∧
        ∀ P L, pubWords≤P → powers≤L → units≤2*L →
          Nonempty (PinStart.PhysicalPost (d:=a.dim) (width:=subt) team a P L
            (cubeCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s (X).frame.width)
            (TeamRowClock.physicalCoefficient a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s)
            pub mac call.val.2.1 call.val.2.2 z) := by
  intro reports
  have generated := prepared_operands_on_visits a team.val offsets ctl live ports owner demand A V seed alloc deck H
    openPlace openReady packet start count stride zero wpos dim width source sortedLo sortedHi ctlLo ctlHi place fit
    pointer controls nc nr cc space placedSide geom extra production
  obtain ⟨ready,words,written⟩ := generated
  have unchanged := CellDispatch.memory_after_owned_calls call.property
  have actual : ReportAllocation a.before a.after banks l reports q := alloc.tape _ _
  have result := localPacketFinish a startup fields pub owner team demand A reports q actual mac call.val.2.1 call.val.2.2
    start count stride zero seed.framePointer.symm layout.1 headEq layout.2 (unchanged.symm ▸ initial)
    (unchanged.symm ▸ ready) (unchanged.symm ▸ words) (by rw [unchanged,←seed.framePointer]; exact written)
    vertices digits ids header position space teamFit subtWidth wpos z
  obtain ⟨receipt,post,_,_,keep,_,cost⟩ := result
  refine ⟨_,receipt,post,keep,?_⟩
  intro pubWords powers units fieldsFit useFit liveUnits verticesFit
  have bound := cost pubWords powers units fieldsFit useFit liveUnits verticesFit
  exact ⟨bound,fun _ _ words slots paid =>
    ⟨⟨_,_,receipt,post,keep,pubWords,powers,units,words,slots,paid,bound⟩⟩⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
