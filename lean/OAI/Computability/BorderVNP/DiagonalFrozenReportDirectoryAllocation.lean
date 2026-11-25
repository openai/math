import OAI.Computability.BorderVNP.DiagonalLocalReportAllocation
import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReportRows
import OAI.Computability.BorderVNP.PackedFrozenNativePort
import OAI.Computability.BorderVNP.ResidueParseReindex

/-! # The chosen frozen report allocation for one local opening -/

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

/-- The frozen task has exactly the original tile roster, magnitude-bit
width and hidden leaf/copy cardinality used in the local allocation. -/
theorem JointSchedule.frozenReportAllocation_shape
    (length : r=stretch b.ρ (k+1)) (chart : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=depth+1)
    (history : leaves=(epochCopies S)^epochs sc.τ (k+1)) (copyCount : copies=TeamScales.width (k+1) sc.α) :
    (task).p.report = reportBounds (task).cube (leaves*GridHosts.tileCount axes depth)
        (seedSiteCapacity (k+1) r axes depth) (task).p.parameters digits (task).p.report.gadgets w ∧
      leaves*copies=(task).cube.teams := by
  have shape := (b.frozenSignedTask_reports cube (k+1) k size headerFactor initial dir profile ceiling outputs field dirs).2.2.2.1
  rw [←length,chart,Nat.add_sub_cancel,←history,←seedPortCount (D:=D) depth] at shape
  refine ⟨shape,?_⟩
  have actual := (b.sizes (Nat.succ_pos k)).1
  change b.physical.teamsPred (k+1)+1=TeamScales.width (k+1) sc.α*(epochCopies S)^epochs sc.τ (k+1) at actual
  rw [history,copyCount,mul_comm]
  exact actual.symm

/-- Allocate the actual compact report rows from one returned native
opening. The team embedding and grammar numbering are those of the frozen
seed plan; the private bank contents can be arbitrary. -/
theorem JointSchedule.frozenReportDirectory_allocation
    (length : r=stretch b.ρ (k+1)) (chart : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=depth+1)
    (history : leaves=(epochCopies S)^epochs sc.τ (k+1)) (copyCount : copies=TeamScales.width (k+1) sc.α)
    (home : Fin J → Fin (task).cube.cells) (axis : Fin ((task).cube.n+1)) (owned : ℕ → ℕ)
    (counts : ℕ → Fin (task).p.report.gadgets → Fin (task).p.report.countWidth → Bool)
    (room : (task).OpenRoom frame offsets ctl live nports J (2^bitWidth) w)
    (place : OpenSuffix.Placement ((task).openInputs team frame offsets ctl live nports J bitWidth home
      (ReportBundle.header ∘ source)) (task).cube (task).before frame owned)
    {wp wd X P L reader : ℕ} (windows : (task).FinishWindows r w wp wd digits X P L reader)
    (supplied : ∀ c : Fin (task).cube.cells, owned (offsets+2*(task).cube.cables+c.val) ≤ TeamScales.width (k+1) (1/5)) :
    let directory := (task).bundleLayout frame ctl J
    let rows := (task).controlRows team frame offsets ctl live nports
    let rep := reportLayout (task).before (task).after frame ctl (task).p.parameters (task).p.siteWidth (task).p.bodyCap (task).cube.stop
    let opened := grouped directory home source (OpenSuffix.hostImage frame owned)
    let original := directoryCells directory rows rep home source opened counts
    ReportAllocation (task).before (task).after ((task).cube.cellWriter frame ctl axis) rep original (task).after.reportCursor := by
  have shapes := b.frozenReportAllocation_shape (size:=size) cube initial dir headerFactor profile ceiling outputs field dirs
    length chart history copyCount
  let teamNumbers := (finProdFinEquiv.trans (finCongr shapes.2)).toEmbedding
  let params := (ParseTable.numberedLabelEquiv (ParseTable.pairedNumbering (k+1)) k size).toEmbedding
  have hr : 1≤r := by rw [length]; exact stretch_one b.ρ (k+1)
  have stride : 3*(r*(k+1))^2+1 ≤ (task).cube.cellStride := by rw [length]; rfl
  exact W.localDirectory_allocation position origin code sites edges ports channels groups slot base bank
    task home teamNumbers params axis owned counts room place shapes.1 windows hr stride supplied

end Diagonal

end BorderVNP
end Computability
end OAI
