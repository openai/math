import OAI.Computability.VPVNP.CompressorBlockSlices

/-!
# Cached physical addresses for a shrinking node reader

After the slot and subdivision visitors finish, the local evaluator needs
direct access to the packed AB and surviving arrays, the chosen arc roles,
and both incidence directories. Fourteen fixed header cells hold these
addresses. The next-level pointer also locates its DFS layer base.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockDataHeads

open BurstRAM PhaseRecipe BlockPlanner Compression ShrinkBlockInputs

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
  (F : DescriptorSpace.Shape) (i : Fin S.steps)

/-- Offsets 40 through 53 in the old level header. -/
def values (origin abArena widthArena slotArena : Expr) : Fin 14 → Expr :=
  let step := i.val
  let a := ShrinkBlockInputs.a i
  let selected := selectedInputs B F i origin
  let slot := SlotLevel.Recipe.counts (slotTemplate i) (slotInputs B F i origin slotArena)
  let term := ShrinkBundlePlan.termInputs step a origin
  ![LevelFields.atLevel (step+1),slot.inverse,BlockSlices.intervals i widthArena,abArena,
    ShrinkBundlePlan.owner step a origin,ShrinkBundlePlan.ranks step a origin,ShrinkBundlePlan.ids
      step a origin,
    ShrinkTermRecipe.dense a term,ShrinkBundlePlan.sorted step a
      origin,ShrinkBundlePlan.prefixStart step a origin,
    ShrinkBundlePlan.abStart step a origin,(ShrinkBundlePlan.abParams step a origin)
      4,SelectedPlan.roleBase selected,slot.rows]

/-- Fourteen visits that publish the shrinking reader's physical addresses at header offsets 40
through 53. -/
def visits (origin abArena widthArena slotArena : Expr) : List Visit :=
  List.ofFn fun j : Fin 14 ↦ BlockPlanner.publish (LevelFields.address i.val (40+j.val))
    (values B F i origin abArena widthArena slotArena j)

theorem visits_length (origin abArena widthArena slotArena : Expr) :
    (visits B F i origin abArena widthArena slotArena).length = 14 := by simp [visits]

theorem field_visit (origin abArena widthArena slotArena : Expr) (j : Fin 14) :
    (visits B F i origin abArena widthArena slotArena)[j.val]'(by simpa only [visits_length]
      using j.isLt) =
    BlockPlanner.publish (LevelFields.address i.val (40+j.val))
      (values B F i origin abArena widthArena slotArena j) :=
  List.getElem_ofFn ..

end CompressorRecords.BlockDataHeads

end

end VPVNP
end Computability
end OAI
