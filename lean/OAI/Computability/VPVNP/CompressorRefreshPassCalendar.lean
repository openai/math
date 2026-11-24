import OAI.Computability.VPVNP.CompressorRefreshHeaderGroup
import OAI.Computability.VPVNP.CompressorPassTimeline

/-! # The initial, selector and final ordinals of a refresh pass -/

namespace OAI
namespace Computability
namespace VPVNP

set_option quotPrecheck false

namespace CompressorRecords.RefreshPass

open BurstRAM Compression DescriptorSpace BlockPlanner PassTimeline

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}
variable (B : S.Templates) (t : ℕ)
local notation "loc" => Located.mk (steps := S.steps) t .refresh
local notation "scr" => BlockProgram.script B

theorem first_eq : (loc).first B =
    (scr).initial.length + t * (scr).block.length + (RefreshHeaders.window B).before.length := by
  change _ = _ + (BlockGroups.refresh B 0).before.length
  rw [BlockGroups.refresh_offset]
  change _ = _ + (((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length + 0)
  rw [Nat.add_zero]
  rfl

theorem finish_eq : (loc).finish B = (scr).initial.length + (t + 1) * (scr).block.length := by
  change (scr).initial.length + t * (scr).block.length +
    ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length +
    (BlockProgram.refresh B).length = _
  have h : (scr).block.length = ((List.finRange S.steps).flatMap (BlockProgram.shrink B)).length +
      (BlockProgram.refresh B).length := List.length_append ..
  rw [Nat.add_mul, one_mul]
  omega

theorem finish_le_total (base positions blocks : ℕ) (ht : t < blocks) :
    (loc).finish B ≤ directoryRows (BlockProgram.layout B base positions blocks) := by
  rw [finish_eq, BlockProgram.directory_rows,(scr).calendar_total]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _

end CompressorRecords.RefreshPass

end VPVNP
end Computability
end OAI
