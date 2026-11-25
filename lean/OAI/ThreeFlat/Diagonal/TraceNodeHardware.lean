import OAI.ThreeFlat.Diagonal.TraceNodeBankLayout
import OAI.ThreeFlat.Diagonal.TraceNodeCompactCode
import OAI.ThreeFlat.Diagonal.PhysicalNodeHardware

namespace OAI
/-! # Exact native hardware for compact node publication at the trace layout -/
namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure RAM.HistoryStageBody.Physical
open TraceNodeHeaders
noncomputable section

/-- Instruction labels, scratch registers and public words in the entire emitted node
publisher. Its code depends only on child, incidence and motif capacities. -/
theorem compactPublish_resources (W ctrl : ℕ) (a : NodeArchive) (n : ℕ) :
    resources (compactPublish W ctrl a n)=
      38+4*(compactRow 0).work+nodeSize a.childCap a.halfCap a.motifCap := by
  simp only [compactPublish,resources_seq,loop_size,node_size,compactScan,resources_scan,
    HeaderScan.binds_closed]
  change (18+4*(compactRow ctrl).work)+(5+(5+(10+nodeSize a.childCap a.halfCap a.motifCap)))=_
  have uniform : (compactRow ctrl).work=(compactRow 0).work := rfl
  rw [uniform];omega

def compactHardware (cap : ℕ) := 38+4*(compactRow 0).work+nodeSize cap cap cap

theorem traceArchive_hardware (w lanes perLane pairs trace tariff cap n : ℕ) :
    resources (compactPublish (64*w) (compactControl w)
      (traceArchive w lanes perLane pairs trace tariff cap cap cap) n)=compactHardware cap :=
  compactPublish_resources (64*w) (compactControl w) (traceArchive w lanes perLane pairs trace tariff cap cap cap) n

theorem compactPublish_le {W ctrl cap n : ℕ} (a : NodeArchive)
    (children : a.childCap≤cap) (halves : a.halfCap≤cap) (motifs : a.motifCap≤cap) :
    resources (compactPublish W ctrl a n)≤38+4*(compactRow 0).work+nodeHardwareBound cap := by
  rw [compactPublish_resources]
  apply Nat.add_le_add_left
  simpa only [node_size] using node_hardware_le (W:=W) a.banks children halves motifs


end
end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
