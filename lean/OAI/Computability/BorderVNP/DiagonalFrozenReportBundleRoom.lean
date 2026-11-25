import OAI.Computability.BorderVNP.DiagonalFrozenSignedTask
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReportRows
import OAI.Computability.BorderVNP.PackedFrozenNativePort
import OAI.Computability.BorderVNP.ResidueParseReindex

/-! # Original signed seed bundles in the frozen report reservation -/

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

/-- The actual seed rows fit the three source-side reserves of the frozen task.
Every leaf contributes a full set of unary uses even when several originals share a destination. -/
theorem JointSchedule.frozenReportBundle_room
    (length : r=stretch b.ρ (k+1))
    (chart : CoverScale.initialDepth (Epoch.Cube D) r (k+1)=depth+1)
    (history : leaves=(epochCopies S)^epochs sc.τ (k+1))
    (teams : leaves*copies=b.physical.teamsPred (k+1)+1)
    {C : ℕ} (owner : Fin J → Fin C) :
    (∀ c : Fin C, supplementWords ((BundleDirectory.sourceRows owner c.val).map source) ≤ (task).p.report.supplementStride) ∧
    (∀ j, (source j).positions.length ≤ (task).p.report.marked) ∧
    (∑ j, (source j).useCount) = (task).p.report.uses := by
  let pars := pairedTableParameters (k+1) size
  have labelCount : Fintype.card (PairedParameters k size)=pars :=
    (Fintype.card_congr (ParseTable.numberedLabelEquiv (ParseTable.pairedNumbering (k+1)) k size)).trans (Fintype.card_fin _)
  have reports := b.frozenSignedTask_reports cube (k+1) k size headerFactor initial dir profile ceiling outputs field dirs
  have shape := reports.2.2.2.1
  have uses := reports.2.2.2.2.1
  rw [←length,chart,Nat.add_sub_cancel,←history,←seedPortCount (D:=D) depth] at shape
  rw [←length,←teams] at uses
  obtain ⟨count,marks,total⟩ := WiredWitness.physicalReportInventory (copies:=copies) (fun _ : Fin leaves => W)
    position origin code (fun _ => sites) (fun _ => edges) ports channels groups slot base bank
  rw [←count] at shape
  refine ⟨fun c => ?_,?_,?_⟩
  · rw [shape]
    apply report_supplement
    exact marks
  · rw [shape]
    exact marks
  · change (∑ j, (source j).useCount) = _ at total
    change (∑ j, (source j).useCount) = leaves*Fintype.card (PairedParameters k size)*Nat.clog 2 (r*(2*k+1)+1)*copies at total
    rw [total,labelCount,uses]
    dsimp only [pars]
    ring

end Diagonal

end BorderVNP
end Computability
end OAI
