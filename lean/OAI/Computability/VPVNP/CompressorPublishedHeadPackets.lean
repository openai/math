import OAI.Computability.VPVNP.CompressorPublishedHeadsRun
import OAI.Computability.VPVNP.CompressorBlockProgram

/-! # Source packets for the term and DFS address publications

The actual block uses four term pointers, then either fourteen shrinking
addresses or one refresh pointer. Each publication retains its input
outside its own field block.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PublishedHeads

open BurstRAM DescriptorSpace BlockPlanner PhaseRecipe SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} (L : Layout) (first step : ℕ) (pub : Fin 5 → Word w) (state : Word w)
    (original : Memory w) (entry : LevelFields.Entry L first pub state original) (hw : 1 < 2^w)

/-- The four expressions published for a term's record head, stride, layout, and absolute
address. -/
def termValues (head stride layout absolute : Expr) : Fin 4 → Expr := ![head,stride,layout,absolute]

include entry hw in
theorem termPointers (head stride layout absolute : Expr) (fit : levelStart L (first+step)+36+4 ≤ 2^w)
    (pitch : Outside (levelStart L (first+step)+36) 4 (pub 1-1).val)
    (stable : ∀ m, Agree (Outside (levelStart L (first+step)+36) 4) m original → ∀ j,
      (termValues head stride layout absolute j).eval pub state m =
        (termValues head stride layout absolute j).eval pub state original) :
    let rhs := termValues head stride layout absolute
    let base := levelStart L (first+step)+36
    Published L pub state original base (fun j ↦ LevelFields.address step (36+j.val)) rhs ∧
      SourceWalk (BlockHeaderRun.OneCall pub state) (BlockProgram.termPointers step head stride layout absolute)
        original (List.ofFn fun j : Fin 4 ↦ report ((base+j.val : ℕ) : Word w) ((rhs j).eval pub state original)) := by
  have h := run_fields L first step 36 pub state original _ entry hw fit pitch stable
  exact ⟨h, h.source⟩

variable {k : Type*} [_root_.Field k] {S : Compression.BlockSchedule k} (B : S.Templates)
    (shape : DescriptorSpace.Shape) (i : Fin S.steps)

include hw in
theorem dataHeads (origin abArena widthArena slotArena : Expr)
    (entry' : LevelFields.Entry L first pub state original) (fit : levelStart L (first+i.val)+40+14 ≤ 2^w)
    (pitch : Outside (levelStart L (first+i.val)+40) 14 (pub 1-1).val)
    (stable : ∀ m, Agree (Outside (levelStart L (first+i.val)+40) 14) m original → ∀ j,
      (BlockDataHeads.values B shape i origin abArena widthArena slotArena j).eval pub state m =
        (BlockDataHeads.values B shape i origin abArena widthArena slotArena j).eval pub state original) :
    let rhs := BlockDataHeads.values B shape i origin abArena widthArena slotArena
    let base := levelStart L (first+i.val)+40
    Published L pub state original base (fun j ↦ LevelFields.address i.val (40+j.val)) rhs ∧
      SourceWalk (BlockHeaderRun.OneCall pub state) (BlockDataHeads.visits B shape i origin abArena widthArena slotArena)
        original (List.ofFn fun j : Fin 14 ↦ report ((base+j.val : ℕ) : Word w) ((rhs j).eval pub state original)) := by
  have h := run_fields L first i.val 40 pub state original _ entry' hw fit pitch stable
  exact ⟨h, h.source⟩

include entry hw in
theorem refreshHead (fit : levelStart L (first+step)+40+1 ≤ 2^w)
    (pitch : Outside (levelStart L (first+step)+40) 1 (pub 1-1).val) :
    let base := levelStart L (first+step)+40
    let next := LevelFields.atLevel (step+1)
    Published L pub state original base (fun j : Fin 1 ↦ LevelFields.address step (40+j.val)) (fun _ ↦ next) ∧
      SourceWalk (BlockHeaderRun.OneCall pub state) [publish (LevelFields.address step 40) next]
        original [report ((base : ℕ) : Word w) (next.eval pub state original)] := by
  have h := run_fields L first step 40 pub state original (fun _ : Fin 1 ↦ LevelFields.atLevel (step+1))
    entry hw fit pitch (fun m frame _ ↦ by
      let e : LevelFields.Entry L first pub state m := ⟨entry.pointer,(frame _ pitch).trans entry.pitch⟩
      rw [LevelFields.eval_atLevel e,LevelFields.eval_atLevel entry])
  refine ⟨h,?_⟩
  simpa only [List.ofFn_succ, Fin.val_zero, Nat.add_zero, List.ofFn_zero] using h.source

end CompressorRecords.PublishedHeads

end VPVNP
end Computability
end OAI
