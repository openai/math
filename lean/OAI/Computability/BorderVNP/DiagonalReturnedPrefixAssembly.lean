import OAI.Computability.BorderVNP.DiagonalPrefixFinishRun
import OAI.Computability.BorderVNP.DiagonalFrozenPrefixFinishCalibration
import OAI.Computability.BorderVNP.DiagonalSourceReturnedInputs

/-! # Building a positive-prefix finish from its returned source reports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open VPVNP.BurstRAM Crossing Diagonal Diagonal.CellEntries DiagonalTallyRAM DiagonalTallyAllocation
open DiagonalTallyMaterialize DiagonalTallyCellReports RoutingISA DiagonalResidueRAM
open TeamContraction.ProcessorSlots TeamContraction.JointHeader TeamContraction.JointHeader.PositiveFields
open RoutingISA.SignedTaskArena RoutingISA.Evaluator FiniteEvaluator NativeAssignments
open scoped BigOperators Classical

open CompactMachine CellMacro.Generator

variable {D w : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits}
    (sa : SignedTaskArena.Layout) {gen : Fragment IO} {n : ℕ} (S : PositiveTeam sa.id gen n w) (pr : S.Prefix) (control fieldWidth bodyCap : ℕ)
set_option quotPrecheck false
set_option autoImplicit false
local notation "pub" => S.pub
local notation "mac" => install gen n S.routines
local notation "visited" => prefixVisits S pr
local notation "reportL" => reportLayout sa.before sa.after (Fin.val (S.pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop
local notation "nteams" => sa.cube.teams
variable {cell : N.Site → Fin sa.cube.cells}
    (id : TableEntry sa.cube.n sa.cube.b sa.cube.h sa.cube.K sa.cube.s → Fin sa.p.report.gadgets)
    (team : Fin sa.cube.header.d → Fin sa.cube.teams)
    (a : Path N cell sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.K sa.cube.s)
    (rc : ReceivedRows (fun _ : Fin sa.cube.teams => reportLayout sa.before sa.after (Fin.val (S.pub 0)) control sa.p.parameters fieldWidth bodyCap sa.cube.stop) sa.cube.cells)
    (t : Fin sa.cube.teams)

local notation "cursor" => sa.after.reportCursor
local notation "data" => pathBanks a sa.cube.header.packetBase sa.cube.singleBank
local notation "X" => gadgetLookup sa pub (Fin.val ∘ team) t.val D data

variable {reserve axes groups cap width : ℕ} (A : StartupArena)
    (p : PositiveFields reserve axes groups cap sa.cube.teams sa.dim width)
local notation "raw" => rawAddress A reserve axes groups cap


set_option synthInstance.maxSize 4000
set_option maxRecDepth 14000
set_option maxHeartbeats 2200000

open SignedPrep

/-- Assemble the selected-team hardware record from the original returned
report cut, the immutable boot and owned deck, the measured public allocation
and the six scalar observations of the native report frame. -/
noncomputable def PrefixFinishRun.ofReportCut
    (src : ∀ u : Fin nteams, ReportAssignments (rc.cells u)) {description : ℕ}
    (cut : ReportArgumentCut (visited).reports (src t) cursor description)
    (bankControl : ℕ) (axis : Fin (sa.cube.n+1))
    (alloc : ReportAllocation sa.before sa.after (sa.cube.cellWriter (pub 0).val bankControl axis)
      reportL (rc.cells t) cursor)
    (sameFrame : (pub 0).val=A.frame)
    (header : HeaderSeed sa p pub raw t.val (visited).arguments.val.2.2)
    (deck : CubePacket.WordPrepared X sa.id pub (visited).owned.val.2.2)
    (inputs : OpenSuffix.Inputs)
    (openFields : OpenSuffix.Ready inputs (pub 0).val (readings (visited).owned.val.2.2) w ∧
      OpenSuffix.Placement inputs sa.cube sa.before (pub 0).val (readings (visited).owned.val.2.2))
    (markBounds : ∀ c∈rc.cells t, ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (offsets ctl live ports query guesses gates : ℕ)
    (addresses : sa.FinishAddresses A ctl reserve axes groups cap width w query guesses gates)
    (report : let bank := readings (visited).reports.val.2.2
      (FragmentRows.Layout.fromFrame (pub 0).val bank).Fits w bank ∧ bank ((pub 0).val+92)=ctl ∧
      (∀ i : Fin 37, bank (ctl+i.val)=sa.controls i.val) ∧
      (FragmentRows.Layout.fromFrame (pub 0).val bank).host.count=sa.cube.cables ∧
      bank ((pub 0).val+9) ≤ sa.cube.maxRows ∧ bank ((pub 0).val+11)=sa.cube.cells)
    {Orig : Type} (placed : ℕ → CellPacket.Placed Orig) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac (visited).reports.val.2.1
      (visited).reports.val.2.2).symm (visited).arguments
      ∃ input : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2, ScheduleClock.ProducedRoster sa
        (sa.controlRows t.val (pub 0).val offsets ctl live ports) (readings parts.1.val.2.2) placed geom extra input)
    (codes : ∀ e,sa.id e=(id e).val) :
    PrefixFinishRun sa S pr control fieldWidth bodyCap id team a rc t
      (fun u => (reportAssignmentEquiv (rc.cells u)).symm (src u)) A p := by
  have placement : sa.SparsePlacement (pub 0).val ctl := sameFrame.symm ▸ addresses.place
  have count : (X).frame.count ≤ sa.p.report.vertices :=
    (CubeAllocation.team_count sa.cube (data).axis (Fin.val ∘ team) t.val).trans_eq addresses.vertices
  exact ⟨sa.cube.cellWriter (pub 0).val bankControl axis,description,cut.seed,cut.chosen,alloc,rfl,rfl,rfl,
    sameFrame,header,deck,
    inputs,openFields.2,openFields.1,addresses.wordPos,addresses.reportDim.le,addresses.reportWidth.le,
    markBounds,offsets,ctl,live,ports,placement.primary,addresses.sortedHi,placement.beforeControl,
    addresses.ctlHi,query,guesses,gates,placement,report.1,report.2.1,report.2.2.1,report.2.2.2.1,
    report.2.2.2.2.1,report.2.2.2.2.2,Orig,placed,geom,extra,production,codes,count,addresses.digitsFit.le,
    addresses.headerSize,addresses.position,addresses.endFit,addresses.teamsFit,addresses.widthFit⟩

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
