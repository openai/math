import OAI.Hierarchy.ProbeFixedStockOperands
import OAI.Hierarchy.ProtocolRAMCalendarStripPublicROM

namespace OAI
/-! # The mounted catalyst directory ends before the private event arena -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard StripChart StockCommit
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)

/-- The reserve-source pass preserves the occurrence directory that the forest reads. -/
theorem forest_header_before (a : Attempt) :
    (StripChart.header F (v.mounted (v.seed P z width) P width) a).stop ≤
      (v.privateArena P z width).first := by
  have native := (congrArg PortHeader.stop (shape_header F (v.nativeBoards P z width) v.mesh
    (v.privateArena P z width) P.joint.initial a).1).symm.le.trans (v.stock_occurrence_end P z width a)
  have same : (StripChart.header F (v.mounted (v.seed P z width) P width) a).stop =
      (StripChart.header F (v.nativeBoards P z width) a).stop := by cases a <;> rfl
  exact same.le.trans native

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
