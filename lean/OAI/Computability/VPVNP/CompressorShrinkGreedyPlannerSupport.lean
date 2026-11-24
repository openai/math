import OAI.Computability.VPVNP.CompressorGreedyPlannerFootprint
import OAI.Computability.VPVNP.CompressorShrinkHeaderReads

/-! # Operand footprints from the published shrinking header -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderGreedyPackets

open BurstRAM Compression BlockPlanner DescriptorSpace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w g start first : ℕ} (X : GreedyArena.ShrinkingState (ShrinkBlockInputs.a i) g)
  {T : IncidenceDirectory w} {L : Layout} {pub : Fin 5 → Word w} {s : Word w} {m : Memory w}

theorem operand_support (h : ShrinkHeaderReads.Header i X T start L first m)
    (entry : LevelFields.Entry L first pub s m) (D : ℕ → Prop) (pitch : D (pub 1-1).val)
    (cells : ∀ n ≤ 60, D (levelStart L (first+i.val)+n)) (j : GreedyVisit.Stage) :
    HeaderOperands.Supported D pub s m (GreedyVisit.visit (BlockProgram.geometry B) i.val (ShrinkBlockInputs.a i)
      (BlockProgram.arena B i.val 0) j) := by
  have field (n : ℕ) (hn : n ≤ 60) : (LevelFields.scalar i.val n).ReadsFrom D pub s m :=
    GreedyVisit.scalar_support D L first i.val n entry pitch (cells n hn) ((Nat.add_le_add_left hn _).trans_lt h.room)
  exact GreedyVisit.planner_reads D pub s m (BlockProgram.geometry B) i.val (ShrinkBlockInputs.a i)
    (BlockProgram.arena B i.val 0) (field 0 (by decide)) (field 1 (by decide)) (field 3 (by decide))
    (fun c => field (54+c.val) (by have := c.isLt; omega)) (field 60 le_rfl) j

end CompressorRecords.ShrinkHeaderGreedyPackets

end

end VPVNP
end Computability
end OAI
