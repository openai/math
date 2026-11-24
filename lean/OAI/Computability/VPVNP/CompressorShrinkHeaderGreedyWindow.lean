import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorScriptWindow

/-! # The nine initial visits in each shrinking substep

The three header workers and six greedy workers occupy a contiguous window
of the full native block. The static phase and the repeated calendar ordinal
are recovered from the lengths of the actual preceding substeps.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkHeaderGreedyPackets

open Compression BlockPlanner DescriptorSpace

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

/-- The three scheduled visits that publish the shrinking substep's input scalars, output
scalars and directory heads. -/
def headers := BlockHeaderPlan.substep (BlockProgram.geometry B) i.val
  (Scalars.Pass.shrink (ShrinkBlockInputs.a i) (ShrinkBlockInputs.b i))

/-- The six greedy visits for this substep, using its old degree exponent and the first scratch
arena of its level. -/
def greedy := GreedyLevelPlan.visits (BlockProgram.geometry B) i.val (ShrinkBlockInputs.a i)
  (BlockProgram.arena B i.val 0)

/-- The first nine visits of the shrinking substep, with the three header publications
preceding the six greedy visits. -/
def visits := headers B i ++ greedy B i

theorem visits_length : (visits B i).length = 9 := rfl

private theorem remaining : ∃ tail, BlockProgram.shrink B i = visits B i ++ tail := by
  unfold BlockProgram.shrink ShrinkBlockInputs.beforeSlices visits headers greedy
  simp only [List.append_assoc]
  exact ⟨_,rfl⟩

/-- Locate the nine header and greedy visits as a consecutive segment of the full block script
at shrinking index `i`. -/
def window : Window (BlockProgram.script B) (visits B i) where
  before := BlockIndex.earlier B i
  after := (remaining B i).choose ++ BlockIndex.later B i
  block := by
    let tail := (remaining B i).choose
    have sub : BlockProgram.shrink B i = visits B i ++ tail := (remaining B i).choose_spec
    exact (BlockIndex.split_block B i).trans ((congrArg
      (fun xs => BlockIndex.earlier B i ++ xs ++ BlockIndex.later B i) sub).trans
      (by simp only [List.append_assoc,tail]))

theorem window_phase (t : ℕ) (j : Fin (visits B i).length) :
    let A := BlockProgram.script B
    let ordinal := A.initial.length+t*A.block.length+(BlockIndex.earlier B i).length+j.val
    (Schedule.Online.calendar A.plan).phase ordinal = ((window B i).index j).val ∧
    (Schedule.Online.calendar A.plan).level ordinal = t := by
  dsimp only
  rw [show (BlockProgram.script B).initial.length+t*(BlockProgram.script B).block.length+
    (BlockIndex.earlier B i).length+j.val = (BlockProgram.script B).initial.length+t*(BlockProgram.script B).block.length+
    ((window B i).position j).val by change _ = _ + ((BlockIndex.earlier B i).length+j.val); omega]
  exact (BlockProgram.script B).block_phase t ((window B i).position j)

end CompressorRecords.ShrinkHeaderGreedyPackets

end

end VPVNP
end Computability
end OAI
