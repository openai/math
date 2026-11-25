import OAI.Computability.BorderVNP.DiagonalReturnedPrefixAssembly
import OAI.Computability.BorderVNP.DiagonalVisitedReaderWords

/-! # Preserving the owned header through the selected report and sparse calls -/

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

/-- Starting at the actual owned cube and header, execute the selected
control, report and sparse argument programs. Their protected-memory bounds
supply the header at the return where the signed tally consumes it. -/
noncomputable def PrefixFinishRun.ofOwnedCut
    (src : ∀ u : Fin nteams, ReportAssignments (rc.cells u)) {description : ℕ}
    (cut : ReportArgumentCut (visited).reports (src t) cursor description)
    (offsets ctl live ports bundles bits₀ : ℕ)
    (owner : Fin bundles → Fin sa.cube.cells) (headers : Fin bundles → Packing.BottomReports.BundleHeader)
    (axis : Fin (sa.cube.n+1))
    (alloc : ReportAllocation sa.before sa.after (sa.cube.cellWriter (pub 0).val ctl axis)
      reportL (rc.cells t) cursor)
    (sameFrame : (pub 0).val=A.frame)
    (header : HeaderSeed sa p pub raw t.val (visited).owned.val.2.2)
    (deck : CubePacket.WordPrepared X sa.id pub (visited).owned.val.2.2)
    (openFields : OpenSuffix.Ready (sa.openInputs t.val (pub 0).val offsets ctl live ports bundles bits₀ owner headers) (pub 0).val (readings (visited).owned.val.2.2) w ∧
      OpenSuffix.Placement (sa.openInputs t.val (pub 0).val offsets ctl live ports bundles bits₀ owner headers) sa.cube sa.before (pub 0).val (readings (visited).owned.val.2.2))
    (markBounds : ∀ c∈rc.cells t, ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
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
  let input := production.choose
  have issued := production.choose_spec
  have kept := ScheduleClock.keptToCalls_on_visits owner headers A visited axis openFields.2 openFields.1
    cut.seed alloc placement report.1 report.2.1 report.2.2.1 report.2.2.2.1 report.2.2.2.2.1
    report.2.2.2.2.2 addresses.endFit addresses.position addresses.controlAbove addresses.geometryAbove
    placed geom extra input issued
  rw [SignedPrep.visitsEquiv_outState] at kept
  have copied := kept.headerSeed p sameFrame addresses.headerSize header
  exact ofReportCut sa S pr control fieldWidth bodyCap id team a rc t A p src cut ctl axis alloc sameFrame
    copied deck _ openFields markBounds offsets ctl live ports query guesses gates addresses report
    placed geom extra ⟨input,issued⟩ codes

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
