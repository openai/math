import OAI.Computability.BorderVNP.DiagonalOwnedPrefixAssembly
import OAI.Computability.BorderVNP.DiagonalFrozenCutHeader

/-! # Finishing the original positive prefix from a returned candidate’s frozen controls -/

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

/-- A frozen candidate already stores the actual selected controls and pointer
on the owned return. It therefore needs only the three original frame sizes
to continue its own emitted reports, cell arguments and tally. -/
noncomputable def PrefixFinishRun.ofCandidateOpen
    (src : ∀ u : Fin nteams, ReportAssignments (rc.cells u)) {description : ℕ}
    {sourceCursor : ReportCursor} (cut : ReportArgumentCut (visited).reports (src t) sourceCursor description)
    (offsets ctl live ports bundles bits₀ : ℕ)
    (owner : Fin bundles → Fin sa.cube.cells) (headers : Fin bundles → Packing.BottomReports.BundleHeader)
    (axis : Fin (sa.cube.n+1))
    (alloc : ReportAllocation sa.before sa.after (sa.cube.cellWriter (pub 0).val ctl axis)
      reportL (rc.cells t) cursor)
    (sameFrame : (pub 0).val=A.frame)
    (header : HeaderSeed sa p pub raw t.val (visited).owned.val.2.2)
    (deck : CubePacket.WordPrepared X sa.id pub (visited).owned.val.2.2)
    {base : ℕ} {supplied : Fin sa.cube.cells → ℕ} {initial : ℕ → ℕ}
    (frozen : TeamContraction.FrozenControlEntry sa (sa.openInputs t.val base offsets ctl live ports bundles bits₀ owner headers)
      base (pub 0).val ctl offsets w supplied initial (readings (visited).owned.val.2.2))
    (controlEnd : ctl+37 ≤ sa.cube.header.header) (controlAt : control=ctl)
    (markBounds : ∀ c∈rc.cells t, ∀ b∈c.bundles, ∀ g∈b.positions, g.parameter<2^w ∧ g.place<w)
    (query guesses gates : ℕ)
    (addresses : sa.FinishAddresses A ctl reserve axes groups cap width w query guesses gates)
    (scalars : let m := readings (visited).owned.val.2.2
      m (base+7)=sa.cube.cables ∧ m (base+9) ≤ sa.cube.maxRows ∧ m (base+11)=sa.cube.cells)
    {Orig : Type} (placed : ℕ → CellPacket.Placed Orig) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (production : let parts := (ScheduleClock.argumentVisitsEquiv pub mac (visited).reports.val.2.1
      (visited).reports.val.2.2).symm (visited).arguments
      ∃ input : ScheduleClock.SparseCallInput pub parts.2.1.val.2.2, ScheduleClock.ProducedRoster sa
        (sa.controlRows t.val (pub 0).val offsets ctl live ports) (readings parts.1.val.2.2) placed geom extra input)
    (codes : ∀ e,sa.id e=(id e).val) :
    PrefixFinishRun sa S pr control fieldWidth bodyCap id team a rc t
      (fun u => (reportAssignmentEquiv (rc.cells u)).symm (src u)) A p := by
  have baseEq := frozen.frame
  subst base
  have restored := cut.header_on_frozen_control sa owner headers (visited).controls (visited).reports
    header frozen controlEnd controlAt alloc rfl scalars.1 scalars.2.1 scalars.2.2
  exact ofOwnedCut sa S pr control fieldWidth bodyCap id team a rc t A p src restored.choose
    offsets ctl live ports bundles bits₀ owner headers axis alloc sameFrame header deck ⟨frozen.ready,frozen.placement⟩
    markBounds query guesses gates addresses restored.choose_spec.2 placed geom extra production codes

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
