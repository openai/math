import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorShrinkSlotScheduledRuns
import OAI.Computability.VPVNP.CompressorScriptWindow

/-! # The selected slot program's exact ordinal interval in the full block -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BlockPlanner Compression ShrinkSlotPlan.Scheduled

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

/-- The fixed descriptor shape for placing this substep's slot calendar in the complete block
program. -/
abbrev space := BlockProgram.geometry B
/-- Address expression for the first scratch table in this shrinking substep. -/
abbrev origin := BlockProgram.arena B i.val 0
/-- The selected-placement input expressions at this substep's scratch origin, including the
source of its layout bit. -/
abbrev selected := ShrinkBlockInputs.selectedInputs B (space B) i (origin B i)

/-- The slot plan instantiated for this block, reading the selected layout and surviving widths
and using the reserved slot arena to build the next level. -/
def plan : Plan :=
  ⟨ShrinkBlockInputs.slotTemplate i,
   ShrinkBlockInputs.slotInputs B (space B) i (origin B i) (BlockProgram.arena B i.val 3),
   SelectedPlan.layout (selected B i),BlockProgram.arena B i.val 2,space B,i.val⟩

/-- The slot interval follows the resident and slice phases of this exact
substep. The following metadata and pointer publishers are outside it. -/
def window : Window (BlockProgram.script B) (order.map (Stage.visit (plan B i))) where
  before := BlockIndex.earlier B i ++ ShrinkBlockInputs.beforeSlices B (space B) i (origin B i) ++
    ShrinkResidentsPlan.visits (selected B i) (BlockProgram.arena B i.val 5) (LevelFields.atLevel i.val)
      (ShrinkBundlePlan.absoluteCD i.val (ShrinkBlockInputs.a i) (origin B i)) (ShrinkBlockInputs.a i) ++
    BlockSlices.visits B (space B) i (origin B i) (BlockProgram.arena B i.val 1) (BlockProgram.arena B i.val 2)
  after := BlockMetadata.visits (space B) i.val B.recordLimit (slotDegree S) .shrink
      (.shrink (ShrinkBlockInputs.a i) (selected B i)) ++
    BlockProgram.termPointers i.val (selected B i).termBase (.lit (selected B i).termStride)
      (SelectedPlan.layout (selected B i)) (ShrinkBundlePlan.absoluteCD i.val (ShrinkBlockInputs.a i) (origin B i)) ++
    BlockDataHeads.visits B (space B) i (origin B i) (BlockProgram.arena B i.val 1)
      (BlockProgram.arena B i.val 2) (BlockProgram.arena B i.val 3) ++ BlockIndex.later B i
  block := by
    change BlockProgram.block B = _
    rw [BlockIndex.split_block B i,order_visits]
    simp only [BlockProgram.shrink,ShrinkBlockInputs.slots,plan,space,origin,selected,List.append_assoc]

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
