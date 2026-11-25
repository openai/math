import OAI.Computability.BorderVNP.DiagonalFrozenReportPreparation
import OAI.Computability.BorderVNP.DiagonalOriginalIssuedExtras
import OAI.Computability.BorderVNP.DiagonalPreparedBundleRows

/-! # The two actual source inputs of the issued sparse report data -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing Cover Packing Packing.DeckGrid PackedHistoryCircuit.Normalized PackedHistoryCircuit.Normalized.SelectedSchedule
open Diagonal.ExternalSew Diagonal.CellEntries BorderVNP.Epoch
open TeamScales TeamContraction ParseBatch ParseBatchVerifier Prewire RoutingISA RoutingISA.SignedTaskArena
open DiagonalTallyAllocation DiagonalTallyCellReports VPVNP
open scoped Classical BigOperators BorderVNP.Epoch.Cube

set_option maxRecDepth 6000
set_option maxHeartbeats 1600000

variable {F K : Type} [Field F] [Field K] {D m : ℕ} [NeZero D] {e : PaidIdentity F D m}
    {S : SiteSchedule e} {extra E dlog Q A B j : ℕ} (cube : FixedCube K)
    {sc : EpochScales S (cube.pred+1) extra} (b : JointSchedule.{0} sc (E+1) dlog Q A B j)
    {k size R r t pins link inner depth J leaves copies : ℕ}
    {Edge : Type} [Fintype Edge] {G : Wiring R r t pins link inner (k+1) Edge}
    {order : Fin (GridHosts.tileCount (Fintype.card (Epoch.Cube D)) depth) ≃ (Fin (Fintype.card (Epoch.Cube D)) → Deck (depth+2))}
    {state : ParseTable.State (Fin (k+1) × Bool) size}
    (W : WiredWitness G (Fin.last k) D (Fintype.card (Epoch.Cube D)) depth order state)
variable (position : (Fin (Fintype.card (Epoch.Cube D)) → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖≤1})
    (origin : Fin J ≃ Fin leaves × (Fin (Fintype.card (Epoch.Cube D)) → Deck (depth+2)))
    (code : PairedParameters k size ↪ ℕ) {ns ne np qe qa : ℕ}
    (sites : (W.routedFine position).Site ↪ Fin ns) (edges : (W.routedFine position).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth G) ↪ Fin np)
    (channels : ((Fin (Fintype.card (Epoch.Cube D)) → Deck (depth+2)) × Direction (Fintype.card (Epoch.Cube D))) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount (Fintype.card (Epoch.Cube D)) depth) ↪ Fin qa)
    (slot base : Fin J → ℕ) (bank : Fin J → ℕ → Bool)
    (initial : TeamContraction.ProcessorSlots.StartupArena) (dir : Directory.Layout)
    (headerFactor profile ceiling outputs field : ℕ) (dirs : GeometryDirectories)
local notation3 (prettyPrint := false) "source" => fun j : Fin J =>
  W.seedUseBundle position code sites edges ports channels groups (origin j).2 (slot j) (base j) copies (bank j)
local notation3 (prettyPrint := false) "task" =>
  b.frozenSignedTask cube (k+1) k size headerFactor initial dir profile ceiling outputs field dirs

open FiniteEvaluator ReportDirectory
variable {frame ctl team offsets live nports bitWidth : ℕ}
local notation "w" => b.physical.word (k+1)
local notation "digits" => Nat.clog 2 (r*(2*k+1)+1)
local notation "axes" => Fintype.card (Epoch.Cube D)


open RoutingOutputs VPVNP.BurstRAM Evaluator TeamContraction TeamContraction.JointHeader
open BorderVNP.Cube.Physical BorderVNP.Cube.Padding.Banks

open Evaluator.ScheduleClock

/-- Read the actual compact native report and the recovered source candidates on the same team. Both the packet issuer and the consuming argument clock receive their own prepared input, allocation and exact supplemental stream. -/
theorem JointSchedule.frozenIssuedReportReadback
    (length : r=stretch b.ρ (k+1)) (chart : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=depth+1)
    (history : leaves=(epochCopies S)^epochs sc.τ (k+1)) (copiesAt : copies=TeamScales.width (k+1) sc.α)
    (u : Fin (R+1)) (address frame nports bitWidth : ℕ) :
    let ar := task
    let wordLen := b.physical.word (k+1)
    let saved := source
    let tables := bases address ar.cube.cables ar.cube.cells J
    let ctrl := controlsBase address ar.cube.cables ar.cube.cells J nports
    let directory := ar.bundleLayout frame ctrl J
    let rows := ar.controlRows u.val frame tables.ends ctrl tables.livePairs nports
    let rep := reportLayout ar.before ar.after frame ctrl ar.p.parameters ar.p.siteWidth ar.p.bodyCap ar.cube.stop
    ∀ (cell : Fin J → Fin ar.cube.cells),
    let prog := ar.openInputs u.val frame tables.ends ctrl tables.livePairs nports J bitWidth cell (ReportBundle.header ∘ saved)
    ∀ (counts : ℕ → Fin ar.p.report.gadgets → Fin ar.p.report.countWidth → Bool) {pub : Arg → Word wordLen}
        {mac : TeamOpcode.Macros wordLen 8} {owned : Memory wordLen} {regs : Bank wordLen},
    let middle := grouped directory cell saved (OpenSuffix.hostImage frame (readings owned))
    let orig := directoryCells directory rows rep cell saved middle counts
    ∀ (coord : Fin (ar.cube.n+1)) (description : ℕ) (ret : Returns SignedPrep.controls pub mac regs owned)
        (prof initialMem written after : ℕ → ℕ) (supplied : Fin ar.cube.cells → ℕ),
      NativeEntry ar.cube frame ctrl coord R prof initialMem written →
      FrozenControlEntry ar prog frame (pub 0).val ctrl tables.ends wordLen supplied written (readings owned) →
      ar.OpenRoom frame tables.ends ctrl tables.livePairs nports J (2^bitWidth) wordLen →
      (∀ c : Fin ar.cube.cells,rows.owner after c.val=(ar.cube.receivingOwner frame coord R prof c.val).val) →
      (∀ c, supplied c ≤ TeamScales.width (k+1) (1/5)) →
      ∀ {wp wd X P L ticks : ℕ}, ar.FinishWindows r wordLen wp wd digits X P L ticks →
      ∀ {reserve nAxis syms cap sub raw : ℕ} {fields₀ : PositiveFields reserve nAxis syms cap ar.cube.teams ar.dim sub},
      HeaderSeed ar fields₀ pub raw u.val owned →
      ∀ (owner : Fin ar.cube.header.d → ℕ) (demand : ℕ)
        (data : Data ar.cube.n ar.cube.header.d ar.cube.header.blocks ar.cube.b ar.cube.h ar.cube.K ar.cube.s),
      CubePacket.WordPrepared (gadgetLookup ar pub owner u.val demand data) ar.id pub owned →
      (∀ j,(∃ c∈orig,(cell j).val=c.number) →
        (saved j).delivered rep description (OpenSuffix.hostImage frame (readings owned)) ∧ (saved j).SiteRoom rep wordLen description) →
      SiteIntervals orig description ar.cube.cellStride →
      (∀ c∈orig,c.privateWires+c.supplied+c.tailWidth<2^wordLen) →
      (ar.p.siteWidth≤wordLen ∧ ar.p.siteWidth+ar.p.bodyCap<2^wordLen) →
      ∀ {inputs guesses gates : ℕ}, ar.endAddress wordLen inputs guesses gates<2^wordLen →
      let selected := sourceCells rep cell saved u.val (rows.owner after) (fun c => ar.cube.cellBank+c*ar.cube.cellStride)
        (fun c => initialMem (tables.ends+2*ar.cube.cables+c)) (fun c => initialMem (tables.livePairs+2*nports+c)) counts
      ∀ (canonical : List (ReportCell rep)), SignedPrep.SameReportCells orig canonical →
      let atCell := sourceCell rep cell saved (fun c => ar.cube.cellBank+c*ar.cube.cellStride)
        (fun c => initialMem (tables.ends+2*ar.cube.cables+c)) (fun c => initialMem (tables.livePairs+2*nports+c)) counts
      let submitted := visitedReportRows rows after atCell
      PreparedReportInput pub ret.val.2.2 selected ar.after.reportCursor description ∧
        ReportAllocation ar.before ar.after (ar.cube.cellWriter frame ctrl coord) rep selected ar.after.reportCursor ∧
        PreparedReportInput pub ret.val.2.2 canonical ar.after.reportCursor description ∧
        ReportAllocation ar.before ar.after (ar.cube.cellWriter frame ctrl coord) rep canonical ar.after.reportCursor ∧
        ar.before.tailWidths=rep.tailWidths ∧ seedExtras canonical ar.after.reportCursor=seedExtras submitted ar.after.reportCursor := by
  intro ar wordLen saved tables ctrl directory rows rep cell prog counts pub mac owned regs middle orig coord description
    ret prof initialMem written after supplied entry frames room who sewn wp wd X P L ticks windows reserve nAxis syms cap sub
    raw fields₀ seed owner demand data deck literals intervals privateFit scanner inputs guesses gates endFit selected
    canonical same atCell submitted
  have actual := b.frozenPreparedSourceCells cube W position origin code sites edges ports channels groups slot
    base bank initial dir headerFactor profile ceiling outputs field dirs length chart history copiesAt u address frame nports bitWidth
    cell counts coord description ret prof initialMem written after supplied entry frames room who sewn windows seed owner demand
    data deck literals intervals privateFit scanner endFit
  have kept : CubeAllocation.HostRetention ar.cube frame initialMem written (readings owned) :=
    ⟨frames.retained.primary,fun i hi lo₁ lo₂ => (frames.retained.lower i hi lo₁ lo₂).trans (entry.low i hi),
      frames.retained.tables⟩
  have spelling : orig=selected := ar.localDirectory_sourceCells u coord cell saved prof initialMem written
    (readings owned) entry kept frames.placement room after who counts
  have sourceSame : SignedPrep.SameReportCells selected canonical := spelling ▸ same
  have ordered : submitted=selected := visitedReportRows_scan rows after atCell
  exact ⟨actual.1,actual.2,sourceSame.source_seed actual.1,sourceSame.source_allocation actual.2,rfl,
    ordered.symm ▸ (sourceSame.seedExtras_eq actual.2).symm⟩

end Diagonal

end BorderVNP
end Computability
end OAI
