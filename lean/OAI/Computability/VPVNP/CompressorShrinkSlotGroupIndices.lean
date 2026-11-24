import OAI.Computability.VPVNP.CompressorShrinkSlotPackets
import OAI.Computability.VPVNP.CompressorShrinkSlotWindow
import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorWindowPackets

/-! # Calendar indices of the 22 selected shrinking slot passes -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkSlotCalendar

open BurstRAM BlockPlanner Compression ShrinkSlotPlan.Scheduled
variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
local notation "W" => window B i
local notation "groupW" => BlockGroups.shrink B i 8

theorem part_eight_before : (W).before.length = (groupW).before.length := by
  rw [BlockGroups.shrink_offset, show (8 : Fin 12).val = 8 from rfl]
  simp only [window,List.length_append,BlockGroups.parts,ShrinkBlockInputs.beforeSlices,
    BlockSlices.visits,space,origin,selected,List.take_succ_cons,List.take_zero,
    List.flatten_cons,List.flatten_nil,List.length_nil,Nat.add_zero]
  omega

/-- Embedding the repeated slot workers in the full block yields precisely
the eighth shrinking part's ordered catalog indices. -/
theorem part_eight_indices {w : ℕ} (s : SlotLevel.Shape) (h : SlotLevel.Heads)
    (side : Bool) (width : ℕ) (dest : IncidenceDirectory w) :
    (List.ofFn (ShrinkSlotPackets.packetVisit (plan B i) W s h side width dest)).map
      (fun v => v.phase) = (groupW).indices := by
  rw [List.map_ofFn,Window.indices]
  have len : order.length = ((BlockGroups.parts B i)[8]'(by rw [BlockGroups.parts_length]; decide)).length := by
    change order.length = (ShrinkBlockInputs.slots B (space B) i (origin B i)
      (BlockProgram.arena B i.val 3) (BlockProgram.arena B i.val 2)).length
    rw [ShrinkBlockInputs.slots_length]
    rfl
  rw [List.ofFn_congr len]
  congr 1
  funext n
  apply Fin.ext
  change (BlockProgram.script B).initial.length+((W).before.length+n.val) =
    (BlockProgram.script B).initial.length+((groupW).before.length+n.val)
  rw [part_eight_before]

end CompressorRecords.ShrinkSlotCalendar

end

end VPVNP
end Computability
end OAI
