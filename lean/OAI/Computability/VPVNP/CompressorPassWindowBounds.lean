import OAI.Computability.VPVNP.CompressorPassTimeline

/-! # The exclusive bound of every located pass in a live block -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PassTimeline

open Compression BlockPlanner

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

theorem Located.finish_le_calendar (z : Located S.steps) (B : S.Templates) {blocks : ℕ} (live : z.block < blocks) :
    z.finish B ≤ (Schedule.Online.calendar (BlockProgram.script B).plan).total blocks := by
  let A := BlockProgram.script B
  have window := congrArg List.length (z.window B).block
  simp only [List.length_append] at window
  have span : (z.window B).before.length + (z.visits B).length ≤ A.block.length := by
    change (z.window B).before.length + (z.visits B).length ≤ (BlockProgram.script B).block.length
    omega
  have nxt := Nat.mul_le_mul_right A.block.length (show z.block+1 ≤ blocks from live)
  rw [Nat.succ_mul] at nxt
  rw [A.calendar_total]
  change A.initial.length + z.block*A.block.length+(z.window B).before.length+(z.visits B).length ≤
    A.initial.length+blocks*A.block.length
  omega

end CompressorRecords.PassTimeline

end VPVNP
end Computability
end OAI
